import ProphetSecretary.Limiting.CountableFiniteMask
import ProphetSecretary.Limiting.CountableContinuationApproximation
import ProphetSecretary.Limiting.HybridZeroOutside
import ProphetSecretary.Limiting.HybridRetainedMonotonicity

/-!
# Ordering remaining masks through actual finite zero-variable simulations

Only laws of removed identities are replaced by deterministic zero. Their
fresh zero observations are retained in the finite comparison and justified by
the proved zero-variable simulation, before the actual countable value limit.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting

def MaskLe (left right : IndividualMask) : Prop := ∀ i, left i = true → right i = true

def finiteMaskSet {N : ℕ} (keep : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun i => keep i = true)

lemma CountableInstance.finiteMaskState_value_eq_zeroOutside (B : CountableInstance) (N : ℕ)
    (b : ℝ) (hb : (B.terminal : ℝ) < b) (keep : Fin N → Bool) (w d : ℝ) (u : ℝ≥0) :
    ((B.finiteMaskState N b hb keep).remainingHorizon u).optimalScalarValue w d =
      (((B.truncation N b hb).remainingHorizon u).zeroOutside (finiteMaskSet keep)).optimalScalarValue w d := by
  apply FiniteIntensityHybridInstance.optimalScalarValue_eq_of_data
  · apply Model.Instance.eq_of_law_eq
    funext i
    change (maskedProbabilityLaw (B.individuals i.val) (extendIndividualMask keep i.val) : Measure ℝ) =
      if i ∈ finiteMaskSet keep then (B.individuals i.val : Measure ℝ) else Measure.dirac 0
    rw [extendIndividualMask_at_prefix]
    by_cases hk : keep i = true
    · have hi : i ∈ finiteMaskSet keep := by
        simpa only [finiteMaskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hk
      rw [if_pos hi]
      have hProb : maskedProbabilityLaw (B.individuals i.val) (keep i) = B.individuals i.val := if_pos hk
      exact congrArg (fun q : ProbabilityMeasure ℝ => (q : Measure ℝ)) hProb
    · have hi : i ∉ finiteMaskSet keep := by
        simpa only [finiteMaskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hk
      rw [if_neg hi]
      have hProb : maskedProbabilityLaw (B.individuals i.val) (keep i) =
          (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := if_neg hk
      exact congrArg (fun q : ProbabilityMeasure ℝ => (q : Measure ℝ)) hProb
  · rfl
  · rfl

lemma CountableInstance.finiteMaskState_value_mono (B : CountableInstance) (hZero : B.terminal = 0)
    (N : ℕ) (b : ℝ) (hb : (B.terminal : ℝ) < b) (left right : IndividualMask) (hMasks : MaskLe left right)
    (u : ℝ≥0) {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    ((B.finiteMaskState N b hb (restrictIndividualMask N left)).remainingHorizon u).optimalScalarValue w d ≤
      ((B.finiteMaskState N b hb (restrictIndividualMask N right)).remainingHorizon u).optimalScalarValue w d := by
  let D := (B.truncation N b hb).remainingHorizon u
  let A := finiteMaskSet (restrictIndividualMask N left)
  let C := finiteMaskSet (restrictIndividualMask N right)
  have hAC : A ⊆ C := by
    intro i hi
    have hi' : left i.val = true := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hMasks i.val hi'⟩
  calc
    _ = (D.zeroOutside A).optimalScalarValue w d := B.finiteMaskState_value_eq_zeroOutside N b hb _ w d u
    _ = (D.restrictIndividuals A).optimalScalarValue w d := D.zeroOutside_value_eq_restrictIndividuals_with_terminal A hw hd
    _ ≤ (D.restrictIndividuals C).optimalScalarValue w d := D.optimalScalarValue_restrictIndividuals_mono hZero hAC hw hd
    _ = (D.zeroOutside C).optimalScalarValue w d := (D.zeroOutside_value_eq_restrictIndividuals_with_terminal C hw hd).symm
    _ = _ := (B.finiteMaskState_value_eq_zeroOutside N b hb _ w d u).symm

theorem CountableInstance.remainingState_value_mono_mask (B : CountableInstance) (hZero : B.terminal = 0)
    (left right : IndividualMask) (hMasks : MaskLe left right) (u : ℝ≥0)
    {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    (B.remainingState left u).optimalScalarValue w d ≤ (B.remainingState right u).optimalScalarValue w d := by
  have hL := (B.remainingState left u).truncation_value_tendsto (fun N : ℕ => N) B.markCutoff
    B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hd
  have hR := (B.remainingState right u).truncation_value_tendsto (fun N : ℕ => N) B.markCutoff
    B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hd
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [] with N
  have hLeft := congrArg (fun D : FiniteIntensityHybridInstance N => D.optimalScalarValue w d)
    (B.remainingState_truncation_eq left u N (B.markCutoff N) (B.terminal_lt_markCutoff N))
  have hRight := congrArg (fun D : FiniteIntensityHybridInstance N => D.optimalScalarValue w d)
    (B.remainingState_truncation_eq right u N (B.markCutoff N) (B.terminal_lt_markCutoff N))
  exact hLeft.le.trans ((B.finiteMaskState_value_mono hZero N (B.markCutoff N) (B.terminal_lt_markCutoff N)
    left right hMasks u hw hd).trans hRight.symm.le)

end ProphetSecretary.Limiting
