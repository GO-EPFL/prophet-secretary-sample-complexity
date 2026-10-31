import ProphetSecretary.Limiting.CountablePrefixLaw
import ProphetSecretary.Limiting.ObservationRestrictions
import ProphetSecretary.Limiting.CountableLocalFiniteness

/-!
# Embedding arbitrary truncated observers into the countable model

The first N individual identities are observed, including their zeros. Only
anonymous marks at most b are ignored. The construction uses actual past
restrictions and proves first-acceptance admissibility from local finiteness.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

variable {N : ℕ} {Seed : Type*}

noncomputable def extendTruncatedRule (π : HybridRule N Seed) (b : ℝ) : CountableRule Seed where
  individual r t i x H ξ := if hi : i < N then
    π.individual r t ⟨i,hi⟩ x (prefixHistory N H) (ξ.restrict (univ ×ˢ Ioi b)) else false
  poisson r t x H ξ := if b < x then
    π.poisson r t x (prefixHistory N H) (ξ.restrict (univ ×ˢ Ioi b)) else false

variable [MeasurableSpace Seed]

lemma extendTruncatedRule_measurable (π : HybridRule N Seed) (hπ : π.IsMeasurable) (b : ℝ) :
    (extendTruncatedRule π b).IsMeasurable := by
  constructor
  · let Ω := Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point)))
    let f : Ω × ℕ → Bool := fun q => (extendTruncatedRule π b).individual
      q.1.1 q.1.2.1 q.2 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2
    have hf : Measurable f := by
      apply measurable_from_prod_countable_left
      intro i
      by_cases hi : i < N
      · have hr : Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) => q.1) := by fun_prop
        have ht : Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) => q.2.1) := by fun_prop
        have hx : Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) => q.2.2.1) := by fun_prop
        have hH : Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) => prefixHistory N q.2.2.2.1) :=
          (measurable_prefixHistory N).comp (by fun_prop)
        have hξ : Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) => q.2.2.2.2.restrict (univ ×ˢ Ioi b)) :=
          (measurable_measureRestriction (MeasurableSet.univ.prod measurableSet_Ioi)).comp (by fun_prop)
        have hI : Measurable (fun _ : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) => (⟨i,hi⟩ : Fin N)) := measurable_const
        have hcomp := hπ.1.comp (hr.prodMk (ht.prodMk (hI.prodMk (hx.prodMk (hH.prodMk hξ)))))
        change Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) =>
          π.individual q.1 q.2.1 ⟨i,hi⟩ q.2.2.1 (prefixHistory N q.2.2.2.1)
            (q.2.2.2.2.restrict (univ ×ˢ Ioi b))) at hcomp
        change Measurable (fun q : Seed × (ℝ × (ℝ × (IndividualHistory × Measure Point))) =>
          (extendTruncatedRule π b).individual q.1 q.2.1 i q.2.2.1 q.2.2.2.1 q.2.2.2.2)
        simp only [extendTruncatedRule,dif_pos hi]
        exact hcomp
      · simp only [f,extendTruncatedRule,dif_neg hi]
        exact measurable_const
    have hg : Measurable (fun q : Seed × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point)))) =>
        ((q.1,(q.2.1,(q.2.2.2.1,(q.2.2.2.2.1,q.2.2.2.2.2)))),q.2.2.1)) := by fun_prop
    exact hf.comp hg
  · let Ω := Seed × (Point × (IndividualHistory × Measure Point))
    have hr : Measurable (fun q : Seed × (Point × (IndividualHistory × Measure Point)) => q.1) := by fun_prop
    have ht : Measurable (fun q : Seed × (Point × (IndividualHistory × Measure Point)) => q.2.1.1) := by fun_prop
    have hx : Measurable (fun q : Seed × (Point × (IndividualHistory × Measure Point)) => q.2.1.2) := by fun_prop
    have hH : Measurable (fun q : Seed × (Point × (IndividualHistory × Measure Point)) => prefixHistory N q.2.2.1) :=
      (measurable_prefixHistory N).comp (by fun_prop)
    have hξ : Measurable (fun q : Seed × (Point × (IndividualHistory × Measure Point)) => q.2.2.2.restrict (univ ×ˢ Ioi b)) :=
      (measurable_measureRestriction (MeasurableSet.univ.prod measurableSet_Ioi)).comp (by fun_prop)
    exact Measurable.ite (measurableSet_lt measurable_const hx)
      (hπ.2.comp (hr.prodMk ((ht.prodMk hx).prodMk (hH.prodMk hξ)))) measurable_const

omit [MeasurableSpace Seed] in
lemma extendTruncatedRule_support (π : HybridRule N Seed) (b : ℝ)
    (v : CompleteWorld Seed) (i : ℕ) (hi : (extendTruncatedRule π b).codeAccepted v i) :
    (∃ j : Fin N, candidateEnumeration (Sum.inl j.val) = i) ∨ b < codeValue v i := by
  have ha := hi.2.2
  cases hc : candidateEnumeration.symm i with
  | inl j =>
    have hsize : j < N := by
      by_contra hn
      simp only [CountableRule.candidateAction,hc,extendTruncatedRule,dif_neg hn] at ha
      cases ha
    left
    refine ⟨⟨j,hsize⟩,?_⟩
    have he := candidateEnumeration.apply_symm_apply i
    rw [hc] at he
    exact he
  | inr kj =>
    right
    by_contra hn
    have hx : ¬b < (candidatePoint v (Sum.inr kj)).2 := by
      simpa only [codeValue,codePoint,hc] using hn
    simp only [CountableRule.candidateAction,hc,extendTruncatedRule,if_neg hx] at ha
    cases ha

lemma extendTruncatedRule_admissible (B : CountableInstance) (π : HybridRule N Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    (extendTruncatedRule π b).Admissible B ν := by
  filter_upwards [B.completeWorld_locallyFinite ν] with v hv
  apply FirstAcceptance.hasFirstIfAccepted_of_finite
  have hprefix : (Set.range (fun j : Fin N => candidateEnumeration (Sum.inl j.val))).Finite := Set.finite_range _
  apply (hprefix.union (hv b hb)).subset
  intro i hi
  change (extendTruncatedRule π b).codeAccepted v i at hi
  rcases extendTruncatedRule_support π b v i hi with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hi.1,h⟩

end ProphetSecretary.Limiting.CountableInstance
