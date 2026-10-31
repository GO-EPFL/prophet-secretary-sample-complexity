import ProphetSecretary.Limiting.TruncatedAcceptedAtoms
import ProphetSecretary.Limiting.AcceptedPointSums

/-!
# The embedded execution has the label-free accepted-point measure

This is a pathwise identity on a genuinely finite upper-band counting measure.
It retains every accepted individual zero if the policy chooses one. The
configuration labels are regrouped analytically and never reach a callback.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

variable {N : ℕ} {Seed : Type*}

private lemma measureSum_onSum {ι κ α : Type*} [MeasurableSpace α] (f : ι ⊕ κ → Measure α) :
    Measure.sum f = Measure.sum (fun i => f (Sum.inl i)) + Measure.sum (fun j => f (Sum.inr j)) := by
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.add_apply,Measure.sum_apply _ hS,Measure.sum_apply _ hS]
  exact ENNReal.summable.tsum_sum ENNReal.summable

lemma extended_pointMeasure_split (π : HybridRule N Seed) (b : ℝ) (v : CompleteWorld Seed)
    (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b)) :
    FirstAcceptance.pointMeasure (extendTruncatedRule π b).codeAccepted codeTime codeValue v =
      (∑ i : Fin N, if π.individualMeasureAccepted (truncatedObserverWorld μ v) i then
        Measure.dirac (v.2.2.1 i.val,v.2.1 i.val) else 0) +
      Measure.sum (fun k => ∑ j : Fin (v.1 k).1,
        if b < ((v.1 k).2 j).2 ∧ π.anonymousMeasureAccepted (truncatedObserverWorld μ v) ((v.1 k).2 j) then
          Measure.dirac ((v.1 k).2 j) else 0) := by
  rw [pointMeasure_eq_acceptedAtoms,measureSum_onSum]
  apply congrArg₂ (fun α β : Measure Point => α + β)
  · calc
      _ = Measure.sum (fun j : ℕ => if hj : j < N then
          (if π.individualMeasureAccepted (truncatedObserverWorld μ v) ⟨j,hj⟩ then
            Measure.dirac (v.2.2.1 j,v.2.1 j) else 0) else 0) := by
        apply congrArg Measure.sum
        funext j
        exact extended_individual_atom π b v μ hμ j
      _ = _ := measureSum_natPrefix N (fun i : Fin N =>
        if π.individualMeasureAccepted (truncatedObserverWorld μ v) i then
          Measure.dirac (v.2.2.1 i.val,v.2.1 i.val) else 0)
  · change Measure.sum (fun p : ℕ × ℕ => (extendTruncatedRule π b).acceptedAtom v (Sum.inr (p.1,p.2))) = _
    rw [← Measure.sum_sum (fun k j => (extendTruncatedRule π b).acceptedAtom v (Sum.inr (k,j)))]
    apply congrArg Measure.sum
    funext k
    calc
      _ = Measure.sum (fun j : ℕ => if hj : j < (v.1 k).1 then
          (if b < ((v.1 k).2 ⟨j,hj⟩).2 ∧
            π.anonymousMeasureAccepted (truncatedObserverWorld μ v) ((v.1 k).2 ⟨j,hj⟩) then
            Measure.dirac ((v.1 k).2 ⟨j,hj⟩) else 0) else 0) := by
        apply congrArg Measure.sum
        funext j
        exact extended_anonymous_atom π b v μ hμ k j
      _ = _ := measureSum_natPrefix (v.1 k).1 (fun j : Fin (v.1 k).1 =>
        if b < ((v.1 k).2 j).2 ∧ π.anonymousMeasureAccepted (truncatedObserverWorld μ v) ((v.1 k).2 j) then
          Measure.dirac ((v.1 k).2 j) else 0)

variable [MeasurableSpace Seed]

lemma acceptedAnonymousMeasure_eq_extended_sum (π : HybridRule N Seed) (hπ : π.IsMeasurable)
    (b : ℝ) (v : CompleteWorld Seed) (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b)) :
    π.acceptedAnonymousMeasure (truncatedObserverWorld μ v) =
      Measure.sum (fun k => ∑ j : Fin (v.1 k).1,
        if b < ((v.1 k).2 j).2 ∧ π.anonymousMeasureAccepted (truncatedObserverWorld μ v) ((v.1 k).2 j) then
          Measure.dirac ((v.1 k).2 j) else 0) := by
  have hA : MeasurableSet {p : Point | π.anonymousMeasureAccepted (truncatedObserverWorld μ v) p} :=
    (π.measurableSet_anonymousMeasureAccepted hπ).preimage measurable_prodMk_left
  have hHigh : MeasurableSet ((univ : Set ℝ) ×ˢ Ioi b) := MeasurableSet.univ.prod measurableSet_Ioi
  change (μ : Measure Point).restrict {p | π.anonymousMeasureAccepted (truncatedObserverWorld μ v) p} = _
  rw [hμ,Measure.restrict_restrict hA,bandCountingMeasure,Measure.restrict_sum _ (hA.inter hHigh)]
  apply congrArg Measure.sum
  funext k
  rw [restricted_countingMeasure (v.1 k) (hA.inter hHigh)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mem_inter_iff,mem_setOf_eq,mem_prod,mem_univ,true_and,mem_Ioi]
  simp only [and_comm]

lemma acceptedPointMeasure_eq_extended_execution (π : HybridRule N Seed) (hπ : π.IsMeasurable)
    (b : ℝ) (v : CompleteWorld Seed) (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b)) :
    (π.acceptedPointMeasure (truncatedObserverWorld μ v) : Measure Point) =
      FirstAcceptance.pointMeasure (extendTruncatedRule π b).codeAccepted codeTime codeValue v := by
  rw [extended_pointMeasure_split π b v μ hμ]
  change (∑ i : Fin N, if π.individualMeasureAccepted (truncatedObserverWorld μ v) i then
      Measure.dirac (v.2.2.1 i.val,v.2.1 i.val) else 0) +
      π.acceptedAnonymousMeasure (truncatedObserverWorld μ v) = _
  rw [acceptedAnonymousMeasure_eq_extended_sum π hπ b v μ hμ]

end ProphetSecretary.Limiting.CountableInstance
