import ProphetSecretary.Statistics.EmpiricalJointMoments
import ProphetSecretary.Statistics.EmpiricalOptimismLower
import ProphetSecretary.Statistics.EmpiricalMomentAbsorption

/-!
# Empirical premium means and localization

At a fixed scalar, averaging the true-law premium sum agrees with the empirical-design
mean. The expected empirical value is controlled by the complete residual envelope.
These identities retain the training/clock integration order and do not condition on
a training-selected scalar.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma empiricalTruePremium_clock_mean (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    (a : (Fin n × Fin k) → ℝ) :
    (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ∂Instance.clocksLaw n) =
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z - z -
        ∫ u, (RandomizedPolicy.waiting n).empiricalClockResidual P z (a, u) ∂Instance.clocksLaw n := by
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm a)
  have hP := P.integrable_maximum_of_bounded hbound
  have hhat : Integrable (Q.unstoppedPremium 1 z) (Instance.clocksLaw n) := by
    simpa only [pow_one] using Q.integrable_unstoppedPremium_pow hQ (by norm_num : (0 : ℝ) < 1) hz 1
  have hW : Integrable (fun u => (RandomizedPolicy.waiting n).empiricalClockResidual (k := k) P z (a, u))
      (Instance.clocksLaw n) :=
    (RandomizedPolicy.waiting n).rule.integrable_clockWeightedResidual (RandomizedPolicy.waiting n).measurable_rule Q P hQ hP
      (RandomizedPolicy.waiting n).seedLaw (by norm_num : (0 : ℝ) < 1) hz
  have heq : (fun u => Q.unstoppedPremiumUnder P 1 z u) =ᵐ[Instance.clocksLaw n]
      (fun u => Q.unstoppedPremium 1 z u - (RandomizedPolicy.waiting n).empiricalClockResidual P z (a, u)) := by
    filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
    have hWsum : (RandomizedPolicy.waiting n).empiricalClockResidual (k := k) P z (a, u) =
        ∑ i : Fin n, Q.transitionResidual P 1 z u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [waiting_clockConditionalReach P u i (hu i).2, one_mul]
    rw [hWsum]
    exact Q.unstoppedPremiumUnder_eq_difference P 1 z u
  have h := integral_congr_ae heq
  rw [integral_sub (f := Q.unstoppedPremium 1 z)
      (g := fun u => (RandomizedPolicy.waiting n).empiricalClockResidual P z (a, u)) hhat hW,
    Q.integral_unstoppedPremium hQ (by norm_num : (0 : ℝ) < 1) hz] at h
  exact h

/-- Exact premium mean after both independent experiments are averaged. -/
theorem Instance.empiricalTruePremiumMoment_one_eq_value (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalTruePremiumMoment k z 1 = P.empiricalScalarValueMoment k z 1 - z := by
  have hUI : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 1
  have hV := empiricalScalarValue_integrable_pow (k := k) P hbound hz 1
  have hVI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using hV
  have hW := (RandomizedPolicy.waiting n).integrable_empiricalClockResidual (k := k) P hbound hz
  have hWI := hW.integral_prod_left
  simp only [Instance.empiricalTruePremiumMoment, Instance.empiricalScalarValueMoment, pow_one]
  rw [integral_prod _ hUI]
  calc
    _ = ∫ a, (optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z - z) -
        (∫ u, (RandomizedPolicy.waiting n).empiricalClockResidual P z (a, u) ∂Instance.clocksLaw n)
          ∂P.trainingCoordinateLaw k := integral_congr_ae (Filter.Eventually.of_forall (empiricalTruePremium_clock_mean P hbound hz))
    _ = _ := by
      rw [integral_sub (f := fun a => optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z - z)
          (g := fun a => ∫ u, (RandomizedPolicy.waiting n).empiricalClockResidual P z (a, u) ∂Instance.clocksLaw n)
          (hVI.sub (integrable_const z)) hWI,
        integral_sub hVI (integrable_const z), integral_const, probReal_univ, one_smul,
        (RandomizedPolicy.waiting n).integral_empiricalClockResidual_zero P hbound hz, sub_zero]

lemma Instance.empiricalScalarValueMoment_one_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalScalarValueMoment k z 1 ≤ optimalScalarValue P 1 z + 2 * P.empiricalSuffixMoment k z 1 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hVI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using empiricalScalarValue_integrable_pow (k := k) P hbound hz 1
  have hEI : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 1
  have hGI := hEI.integral_prod_left
  have h : (∫ a, optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k) ≤
      ∫ a, optimalScalarValue P 1 z + 2 * (∫ u,
        (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n)
        ∂P.trainingCoordinateLaw k := by
    apply integral_mono hVI ((integrable_const _).add (hGI.const_mul 2))
    intro a
    have h := (abs_le.mp ((totalEmpiricalInstance (reservoirCoordinates.symm a)).abs_value_difference_le_residualSuffix P
      (totalEmpiricalInstance_integrable _) hP (by norm_num : (0 : ℝ) < 1) hz)).2
    simp only [Pi.add_apply] at *
    change optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ≤ optimalScalarValue P 1 z + 2 * (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n)
    simp only [Instance.expectedResidualSuffixEnvelope] at h
    linarith
  rw [integral_add (f := fun _ => optimalScalarValue P 1 z)
      (g := fun a => 2 * (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n))
      (integrable_const _) (hGI.const_mul 2), integral_const, probReal_univ, one_smul, integral_const_mul] at h
  have he : P.empiricalSuffixMoment k z 1 =
      ∫ a, (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n)
        ∂P.trainingCoordinateLaw k := by
    simpa only [Instance.empiricalSuffixMoment, pow_one] using integral_prod _ hEI
  rw [← he] at h
  simpa only [Instance.empiricalScalarValueMoment, pow_one] using h

lemma Instance.empiricalTruePremiumMoment_one_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalTruePremiumMoment k z 1 ≤ optimalScalarValue P 1 z + 2 * Real.sqrt (P.empiricalSuffixMoment k z 2) := by
  have h1 := P.empiricalTruePremiumMoment_one_eq_value (k := k) hbound hz
  have h2 := P.empiricalScalarValueMoment_one_le (k := k) hbound hz
  have hI1 : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 1
  have hs : P.empiricalSuffixMoment k z 1 ≤ Real.sqrt (P.empiricalSuffixMoment k z 2) := by
    simpa only [Instance.empiricalSuffixMoment, pow_one] using
      ProphetSecretary.Statistics.integral_le_sqrt_second _ hI1 (empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 2)
  linarith

/-- Jensen and the pointwise residual comparison control the reoptimized empirical
value's cubic moment at a fixed scalar. -/
theorem Instance.empiricalScalarValueMoment_three_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalScalarValueMoment k z 3 ≤ 4 * optimalScalarValue P 1 z ^ 3 + 32 * P.empiricalSuffixMoment k z 3 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hv : 0 ≤ optimalScalarValue P 1 z := optimalScalarValue_nonnegative P hP zero_le_one hz
  have hE1 : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 1
  have hE3 := empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 3
  have hV3 := empiricalScalarValue_integrable_pow (k := k) P hbound hz 3
  have hpoint : ∀ᵐ a ∂P.trainingCoordinateLaw k,
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ^ 3 ≤
        4 * optimalScalarValue P 1 z ^ 3 + 32 * (∫ u,
          (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n) := by
    filter_upwards [hE1.prod_right_ae, hE3.prod_right_ae] with a hI1 hI3
    let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
    let g := ∫ u, Q.residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n
    have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm a)
    have hvQ := optimalScalarValue_nonnegative Q hQ zero_le_one hz
    have hg : 0 ≤ g := integral_nonneg (fun _ => ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)
    have hcomp : optimalScalarValue Q 1 z - optimalScalarValue P 1 z ≤ 2 * g :=
      (abs_le.mp (Q.abs_value_difference_le_residualSuffix P hQ hP (by norm_num : (0 : ℝ) < 1) hz)).2
    have hval : optimalScalarValue Q 1 z ≤ optimalScalarValue P 1 z + 2 * g := by linarith
    have hpow := pow_le_pow_left₀ hvQ hval 3
    have hadd := ProphetSecretary.Statistics.cube_add_le_four_cubes hv (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg)
    have hjensen : g ^ 3 ≤ ∫ u, Q.residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n :=
      ProphetSecretary.Statistics.cube_integral_le_integral_cube (Instance.clocksLaw n)
        (Filter.Eventually.of_forall (fun _ => ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)) hI1 hI3
    nlinarith
  have h := integral_mono_ae hV3 ((integrable_const _).add (hE3.integral_prod_left.const_mul 32)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun _ => 4 * optimalScalarValue P 1 z ^ 3)
      (g := fun a => 32 * (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n))
      (integrable_const _) (hE3.integral_prod_left.const_mul 32), integral_const, probReal_univ, one_smul, integral_const_mul] at h
  have he : P.empiricalSuffixMoment k z 3 =
      ∫ a, (∫ u, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n)
        ∂P.trainingCoordinateLaw k := integral_prod _ hE3
  rw [← he] at h
  exact h

/-- The true-law premium cubic moment is controlled by the true value and the
square root of the sixth suffix moment, with explicit constants. -/
theorem Instance.empiricalTruePremiumMoment_three_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalTruePremiumMoment k z 3 ≤ 208 * optimalScalarValue P 1 z ^ 3 +
      1668 * Real.sqrt (P.empiricalSuffixMoment k z 6) := by
  have hU3 := empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 3
  have hH3 := empiricalDesignPremium_joint_integrable_pow (k := k) P hbound hz 3
  have hE3 := empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 3
  have hE6 := empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 6
  have hraw : P.empiricalTruePremiumMoment k z 3 ≤ 4 * P.empiricalDesignPremiumMoment k z 3 +
      4 * P.empiricalSuffixMoment k z 3 := by
    have h : (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
        (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2 ^ 3
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        ∫ v, 4 * (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremium 1 z v.2 ^ 3 +
          4 * (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ^ 3
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
      apply integral_mono hU3 ((hH3.const_mul 4).add (hE3.const_mul 4))
      intro v
      let Q := totalEmpiricalInstance (reservoirCoordinates.symm v.1)
      have hrel := Q.unstoppedPremiumUnder_eq_difference P 1 z v.2
      have hfull : |∑ i : Fin n, Q.transitionResidual P 1 z v.2 i| ≤ Q.residualSuffixEnvelope P 1 z v.2 :=
        ProphetSecretary.Statistics.le_suffixEnvelope v.2 (Q.transitionResidual P 1 z v.2) none
      have hle : Q.unstoppedPremiumUnder P 1 z v.2 ≤ Q.unstoppedPremium 1 z v.2 + Q.residualSuffixEnvelope P 1 z v.2 := by
        have h := (abs_le.mp hfull).1
        linarith
      have hpow := pow_le_pow_left₀ (Q.unstoppedPremiumUnder_nonnegative P 1 z v.2) hle 3
      have hadd := ProphetSecretary.Statistics.cube_add_le_four_cubes (Q.unstoppedPremium_nonnegative 1 z v.2)
        (ProphetSecretary.Statistics.suffixEnvelope_nonnegative v.2 (Q.transitionResidual P 1 z v.2))
      change Q.unstoppedPremiumUnder P 1 z v.2 ^ 3 ≤ 4 * Q.unstoppedPremium 1 z v.2 ^ 3 + 4 * Q.residualSuffixEnvelope P 1 z v.2 ^ 3
      exact hpow.trans hadd
    have he := integral_add (hH3.const_mul 4) (hE3.const_mul 4)
    rw [he, integral_const_mul, integral_const_mul] at h
    exact h
  have hKac := P.empiricalDesignPremiumMoment_three_le (k := k) hbound hz
  have hVal := P.empiricalScalarValueMoment_three_le (k := k) hbound hz
  have hRoot : P.empiricalSuffixMoment k z 3 ≤ Real.sqrt (P.empiricalSuffixMoment k z 6) := by
    simpa only [Instance.empiricalSuffixMoment] using
      ProphetSecretary.Statistics.integral_cube_le_sqrt_sixth _ hE3 hE6
  nlinarith

end ProphetSecretary.Model
