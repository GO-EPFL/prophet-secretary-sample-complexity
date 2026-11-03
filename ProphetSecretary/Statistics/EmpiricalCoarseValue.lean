import ProphetSecretary.Statistics.EmpiricalPremiumRelations

/-!
# A dimension-free coarse empirical value estimate

Averaging the unstopped premium sum gives the empirical value minus the waiting
payoff. Unit-capped observations bound this premium mean by one, so the reverse
martingale second moment gives the `4 / sqrt(m)` bound of
`lem:empirical-value-coarse` without a total-first-moment assumption.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.empiricalScalarValueMoment_one_le_unit (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalScalarValueMoment k z 1 ≤ 1+z := by
  have hVI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z)
      (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using empiricalScalarValue_integrable_pow (k := k) P hcap hz 1
  have h := integral_mono_ae hVI (integrable_const (1+z)) (by
    filter_upwards [trainingCoordinates_unit_ae (k := k) P hcap] with a ha
    let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
    have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm a)
    have hQB := totalEmpiricalInstance_bounded (reservoirCoordinates.symm a) zero_le_one
      (fun i j => ha i j)
    have hM := Q.expectedMaximum_le_of_bounded zero_le_one hQB
    have hValue := optimalScalarValue_le_benchmark Q hQ zero_le_one hz
    change optimalScalarValue Q 1 z ≤ 1+z
    nlinarith)
  simpa only [Instance.empiricalScalarValueMoment, pow_one, integral_const, probReal_univ, one_smul] using h

lemma Instance.empiricalTruePremiumMoment_one_le_unit (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalTruePremiumMoment k z 1 ≤ 1 := by
  rw [P.empiricalTruePremiumMoment_one_eq_value hcap hz]
  linarith [P.empiricalScalarValueMoment_one_le_unit (k := k) hcap hz]

lemma Instance.empiricalSuffixMoment_two_le_unit (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalSuffixMoment k z 2 ≤ 4/(k : ℝ) := by
  have h := P.empiricalSuffixMoment_two_le (k := k) hcap hz
  have hU := P.empiricalTruePremiumMoment_one_le_unit (k := k) hcap hz
  have hScale := mul_le_mul_of_nonneg_left hU (by positivity : (0 : ℝ) ≤ 4/(k : ℝ))
  exact h.trans (by simpa only [mul_one] using hScale)

/-- The coarse value error is independent of both dimension and the scalar coefficient. -/
theorem Instance.empiricalScalarValue_L1_error_le (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    (∫ a : (Fin n × Fin k) → ℝ,
      |optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z -
        optimalScalarValue P 1 z| ∂P.trainingCoordinateLaw k) ≤ 4/Real.sqrt (k : ℝ) := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hVI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z)
      (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using empiricalScalarValue_integrable_pow (k := k) P hcap hz 1
  have hE1 : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using empiricalSuffix_joint_integrable_pow (k := k) P hcap hz 1
  have hE2 := empiricalSuffix_joint_integrable_pow (k := k) P hcap hz 2
  have hMean : P.empiricalSuffixMoment k z 1 ≤ Real.sqrt (4/(k : ℝ)) := by
    have h := ProphetSecretary.Statistics.integral_le_sqrt_second
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) hE1 hE2
    have h' : P.empiricalSuffixMoment k z 1 ≤ Real.sqrt (P.empiricalSuffixMoment k z 2) := by
      simpa only [Instance.empiricalSuffixMoment, pow_one] using h
    exact h'.trans (Real.sqrt_le_sqrt (P.empiricalSuffixMoment_two_le_unit (k := k) hcap hz))
  have hErr := integral_mono (hVI.sub (integrable_const _)).abs
    (hE1.integral_prod_left.const_mul 2) (fun a =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).abs_value_difference_le_residualSuffix P
        (totalEmpiricalInstance_integrable _) hP zero_lt_one hz)
  have he : P.empiricalSuffixMoment k z 1 =
      ∫ a, (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u
        ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k := by
    simpa only [Instance.empiricalSuffixMoment, pow_one] using integral_prod _ hE1
  rw [integral_const_mul, ← he] at hErr
  have hUpper := hErr.trans (mul_le_mul_of_nonneg_left hMean (by norm_num : (0 : ℝ) ≤ 2))
  apply hUpper.trans_eq
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

end ProphetSecretary.Model
