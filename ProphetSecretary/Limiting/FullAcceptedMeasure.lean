import ProphetSecretary.Limiting.TruncatedAcceptedAtoms
import ProphetSecretary.Limiting.AcceptedPointSums

/-!
# The complete countable accepted-point measure

Individual identities remain distinct, including zero observations. Anonymous
labels disappear only in this analytical regrouping: their common callback
depends on the current point and the actual strict counting-measure past.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed : Type*}

noncomputable def CountableRule.individualActionAccepted (π : CountableRule Seed)
    (v : CompleteWorld Seed) (i : ℕ) : Prop :=
  v.2.2.1 i ∈ Icc (0 : ℝ) 1 ∧ π.individual v.2.2.2 (v.2.2.1 i) i (v.2.1 i)
    (individualHistory v.2.1 v.2.2.1 (v.2.2.1 i)) (anonymousHistory v.1 (v.2.2.1 i)) = true

noncomputable def CountableRule.anonymousActionAccepted (π : CountableRule Seed)
    (v : CompleteWorld Seed) (p : Point) : Prop :=
  p.1 ∈ Icc (0 : ℝ) 1 ∧ π.poisson v.2.2.2 p.1 p.2
    (individualHistory v.2.1 v.2.2.1 p.1) (anonymousHistory v.1 p.1) = true

lemma CountableRule.individualAccepted_iff (π : CountableRule Seed) (v : CompleteWorld Seed) (i : ℕ) :
    π.codeAccepted v (candidateEnumeration (Sum.inl i)) ↔ π.individualActionAccepted v i := by
  simp only [CountableRule.codeAccepted,codePresent,codeTime,codePoint,Equiv.symm_apply_apply,
    candidatePresent,candidatePoint,true_and,CountableRule.candidateAction]
  rfl

lemma CountableRule.anonymousAccepted_iff (π : CountableRule Seed) (v : CompleteWorld Seed)
    (k : ℕ) (j : Fin (v.1 k).1) :
    π.codeAccepted v (candidateEnumeration (Sum.inr (k,j.val))) ↔ π.anonymousActionAccepted v ((v.1 k).2 j) := by
  simp only [CountableRule.codeAccepted,codePresent,codeTime,codePoint,Equiv.symm_apply_apply,
    candidatePresent,candidatePoint,CountableRule.candidateAction,configurationPoint,j.isLt,true_and]
  rfl

lemma CountableRule.individualAcceptedAtom (π : CountableRule Seed) (v : CompleteWorld Seed) (i : ℕ) :
    π.acceptedAtom v (Sum.inl i) = if π.individualActionAccepted v i then Measure.dirac (v.2.2.1 i,v.2.1 i) else 0 := by
  simp only [CountableRule.acceptedAtom,π.individualAccepted_iff v i,candidatePoint]

lemma CountableRule.anonymousAcceptedAtom (π : CountableRule Seed) (v : CompleteWorld Seed) (k j : ℕ) :
    π.acceptedAtom v (Sum.inr (k,j)) = if hj : j < (v.1 k).1 then
      (if π.anonymousActionAccepted v ((v.1 k).2 ⟨j,hj⟩) then Measure.dirac ((v.1 k).2 ⟨j,hj⟩) else 0) else 0 := by
  by_cases hj : j < (v.1 k).1
  · rw [dif_pos hj,CountableRule.acceptedAtom,π.anonymousAccepted_iff v k ⟨j,hj⟩]
    simp only [candidatePoint,configurationPoint,dif_pos hj]
  · have hnot : ¬π.codeAccepted v (candidateEnumeration (Sum.inr (k,j))) := by
      intro h
      exact hj (by simpa only [codePresent,Equiv.symm_apply_apply,candidatePresent] using h.1)
    rw [dif_neg hj,CountableRule.acceptedAtom,if_neg hnot]

lemma CountableRule.pointMeasure_split (π : CountableRule Seed) (v : CompleteWorld Seed) :
    FirstAcceptance.pointMeasure π.codeAccepted codeTime codeValue v =
      Measure.sum (fun i => if π.individualActionAccepted v i then Measure.dirac (v.2.2.1 i,v.2.1 i) else 0) +
      Measure.sum (fun k => ∑ j : Fin (v.1 k).1,
        if π.anonymousActionAccepted v ((v.1 k).2 j) then Measure.dirac ((v.1 k).2 j) else 0) := by
  rw [pointMeasure_eq_acceptedAtoms]
  have hfun : π.acceptedAtom v = Sum.elim (fun i => π.acceptedAtom v (Sum.inl i))
      (fun kj => π.acceptedAtom v (Sum.inr kj)) := by funext c; cases c <;> rfl
  rw [hfun,measureSum_sumElim]
  apply congrArg₂ (fun α β : Measure Point => α + β)
  · exact congrArg Measure.sum (funext (π.individualAcceptedAtom v))
  · change Measure.sum (fun p : ℕ × ℕ => π.acceptedAtom v (Sum.inr (p.1,p.2))) = _
    rw [← Measure.sum_sum (fun k j => π.acceptedAtom v (Sum.inr (k,j)))]
    apply congrArg Measure.sum
    funext k
    calc
      _ = Measure.sum (fun j => if hj : j < (v.1 k).1 then
          (if π.anonymousActionAccepted v ((v.1 k).2 ⟨j,hj⟩) then Measure.dirac ((v.1 k).2 ⟨j,hj⟩) else 0) else 0) :=
        congrArg Measure.sum (funext (π.anonymousAcceptedAtom v k))
      _ = _ := measureSum_natPrefix (v.1 k).1 (fun j : Fin (v.1 k).1 =>
        if π.anonymousActionAccepted v ((v.1 k).2 j) then Measure.dirac ((v.1 k).2 j) else 0)

variable [MeasurableSpace Seed]

lemma CountableRule.measurableSet_anonymousActionAccepted (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (v : CompleteWorld Seed) : MeasurableSet {p : Point | π.anonymousActionAccepted v p} := by
  have hH : Measurable (fun p : Point => individualHistory v.2.1 v.2.2.1 p.1) :=
    measurable_individualHistory (fun _ => measurable_const) (fun _ => measurable_const) measurable_fst
  have hξ : Measurable (fun p : Point => anonymousHistory v.1 p.1) :=
    measurable_anonymousHistory measurable_const measurable_fst
  have hr : Measurable (fun _ : Point => v.2.2.2) := measurable_const
  have ha := hπ.2.comp (hr.prodMk ((measurable_fst.prodMk measurable_snd).prodMk (hH.prodMk hξ)))
  exact (measurable_fst measurableSet_Icc).inter (ha (measurableSet_singleton true))

lemma CountableRule.pointMeasure_eq_individuals_add_cloud (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (v : CompleteWorld Seed) :
    FirstAcceptance.pointMeasure π.codeAccepted codeTime codeValue v =
      Measure.sum (fun i => if π.individualActionAccepted v i then Measure.dirac (v.2.2.1 i,v.2.1 i) else 0) +
      (bandCountingMeasure v.1).restrict {p | π.anonymousActionAccepted v p} := by
  rw [π.pointMeasure_split v,bandCountingMeasure,Measure.restrict_sum _ (π.measurableSet_anonymousActionAccepted hπ v)]
  apply congrArg (fun μ : Measure Point => _ + μ)
  apply congrArg Measure.sum
  funext k
  exact (restricted_countingMeasure (v.1 k) (π.measurableSet_anonymousActionAccepted hπ v)).symm

end ProphetSecretary.Limiting.CountableInstance
