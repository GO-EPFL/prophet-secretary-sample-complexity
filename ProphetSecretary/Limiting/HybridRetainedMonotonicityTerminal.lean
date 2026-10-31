import ProphetSecretary.Limiting.HybridRetainedMonotonicity
import ProphetSecretary.Limiting.HybridReserveShift
import ProphetSecretary.Limiting.HybridZeroOutside

/-!
# Retained-state monotonicity with a terminal reserve

Reserve removal commutes with restricting retained identities. The common
terminal contribution cancels, leaving the proved zero-terminal comparison.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma FiniteIntensityHybridInstance.restrictIndividuals_excessState_value
    (B : FiniteIntensityHybridInstance n) (A : Finset (Fin n)) (a : ℝ≥0) (w c : ℝ) :
    ((B.excessState a).restrictIndividuals A).optimalScalarValue w c =
      ((B.restrictIndividuals A).excessState a).optimalScalarValue w c := by
  apply FiniteIntensityHybridInstance.optimalScalarValue_eq_of_data
  · apply Model.Instance.eq_of_law_eq
    funext i
    rfl
  · rfl
  · rfl

theorem FiniteIntensityHybridInstance.optimalScalarValue_restrictIndividuals_mono_with_terminal
    (B : FiniteIntensityHybridInstance n) {A D : Finset (Fin n)} (hAD : A ⊆ D)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.restrictIndividuals A).optimalScalarValue w c ≤
      (B.restrictIndividuals D).optimalScalarValue w c := by
  by_cases hw0 : w = 0
  · subst w
    rw [(B.restrictIndividuals A).value_zero_rewardWeight hc,
      (B.restrictIndividuals D).value_zero_rewardWeight hc]
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have h := (B.excessState B.terminal).optimalScalarValue_restrictIndividuals_mono
    rfl hAD hw hc
  rw [B.restrictIndividuals_excessState_value A B.terminal w c,
    B.restrictIndividuals_excessState_value D B.terminal w c] at h
  rw [(B.restrictIndividuals A).value_reserveShift hwP hc,
    (B.restrictIndividuals D).value_reserveShift hwP hc]
  change w * (B.terminal : ℝ) +
      ((B.restrictIndividuals A).excessState B.terminal).optimalScalarValue w c ≤
    w * (B.terminal : ℝ) +
      ((B.restrictIndividuals D).excessState B.terminal).optimalScalarValue w c
  linarith only [h]

theorem FiniteIntensityHybridInstance.valueHybridThreshold_monotone_with_terminal
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    MonotoneHybridThresholds (B.valueHybridThreshold w c) := by
  intro _r t _ht
  constructor
  · intro i A D _hi hAD
    apply div_le_div_of_nonneg_right _ hw.le
    exact (B.remainingHorizon (remainingTime t)).optimalScalarValue_restrictIndividuals_mono_with_terminal
      (Finset.erase_subset_erase i hAD) hw.le (mul_nonneg hc (remainingTime t).property)
  · intro A D hAD
    apply div_le_div_of_nonneg_right _ hw.le
    exact (B.remainingHorizon (remainingTime t)).optimalScalarValue_restrictIndividuals_mono_with_terminal
      hAD hw.le (mul_nonneg hc (remainingTime t).property)

theorem FiniteIntensityHybridInstance.valueRule_strict_retained_reach_with_terminal
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (i : Fin n) :
    (B.valueRule w c).individualReachProbability P μ (Measure.dirac ()) i -
      (B.valueRule w c).meanDuration P μ (Measure.dirac ()) ≥
      ((B.valueRule w c).individualSelectionProbability P μ (Measure.dirac ()) i)^2 / 2 := by
  exact hybridThresholdRule_strict_reach _ (B.valueHybridThreshold_monotone_with_terminal hw hc)
    (B.valueRule_isMeasurable hw.le hc) P μ (Measure.dirac ()) i

end ProphetSecretary.Limiting
