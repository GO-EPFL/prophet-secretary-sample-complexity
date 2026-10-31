import ProphetSecretary.Statistics.MixedEmpiricalJointMoments
import ProphetSecretary.Statistics.MixedEmpiricalClockResidual
import ProphetSecretary.Statistics.EmpiricalMomentAbsorption

/-!
# Fixed-scalar mixed premium mean and localization relations

Actual zero mean of the signed reverse residual identifies the average true
premium with the mixed design mean. The generic Bellman residual comparison,
Jensen and Kac estimates then control first and cubic moments. Known laws are
exact throughout; no scalar selected from training is centered here.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedTruePremium_clock_mean (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    (a : (Fin n × Fin k) → ℝ) :
    (∫ u, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ∂Instance.clocksLaw n) =
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z - z -
        ∫ u, (RandomizedPolicy.waiting n).mixedClockResidual P known z (a, u) ∂Instance.clocksLaw n := by
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
  have hQ := mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known (reservoirCoordinates.symm a)
  have hP := P.integrable_maximum_of_bounded hbound
  have hhat : Integrable (Q.unstoppedPremium 1 z) (Instance.clocksLaw n) := by
    simpa only [pow_one] using Q.integrable_unstoppedPremium_pow hQ (by norm_num : (0 : ℝ) < 1) hz 1
  have hW : Integrable (fun u => (RandomizedPolicy.waiting n).mixedClockResidual (k := k) P known z (a, u))
      (Instance.clocksLaw n) :=
    (RandomizedPolicy.waiting n).rule.integrable_clockWeightedResidual (RandomizedPolicy.waiting n).measurable_rule Q P hQ hP
      (RandomizedPolicy.waiting n).seedLaw (by norm_num : (0 : ℝ) < 1) hz
  have heq : (fun u => Q.unstoppedPremiumUnder P 1 z u) =ᵐ[Instance.clocksLaw n]
      (fun u => Q.unstoppedPremium 1 z u - (RandomizedPolicy.waiting n).mixedClockResidual P known z (a, u)) := by
    filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
    have hWsum : (RandomizedPolicy.waiting n).mixedClockResidual (k := k) P known z (a, u) =
        ∑ i : Fin n, Q.transitionResidual P 1 z u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [waiting_clockConditionalReach P u i (hu i).2, one_mul]
    rw [hWsum]
    exact Q.unstoppedPremiumUnder_eq_difference P 1 z u
  have h := integral_congr_ae heq
  rw [integral_sub (f := Q.unstoppedPremium 1 z)
      (g := fun u => (RandomizedPolicy.waiting n).mixedClockResidual P known z (a, u)) hhat hW,
    Q.integral_unstoppedPremium hQ (by norm_num : (0 : ℝ) < 1) hz] at h
  exact h

/-- Exact premium mean after both independent experiments are averaged. -/
theorem Instance.mixedTruePremiumMoment_one_eq_value (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedTruePremiumMoment known k z 1 = P.mixedScalarValueMoment known k z 1 - z := by
  have hUI : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using mixedTruePremium_joint_integrable_pow (k := k) P known hbound hz 1
  have hV := mixedScalarValue_integrable_pow (k := k) P known hbound hz 1
  have hVI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using hV
  have hW := (RandomizedPolicy.waiting n).integrable_mixedClockResidual (k := k) P known hbound hz
  have hWI := hW.integral_prod_left
  simp only [Instance.mixedTruePremiumMoment, Instance.mixedScalarValueMoment, pow_one]
  rw [integral_prod _ hUI]
  calc
    _ = ∫ a, (optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z - z) -
        (∫ u, (RandomizedPolicy.waiting n).mixedClockResidual P known z (a, u) ∂Instance.clocksLaw n)
          ∂P.trainingCoordinateLaw k := integral_congr_ae (Filter.Eventually.of_forall (mixedTruePremium_clock_mean P known hbound hz))
    _ = _ := by
      rw [integral_sub (f := fun a => optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z - z)
          (g := fun a => ∫ u, (RandomizedPolicy.waiting n).mixedClockResidual P known z (a, u) ∂Instance.clocksLaw n)
          (hVI.sub (integrable_const z)) hWI,
        integral_sub hVI (integrable_const z), integral_const, probReal_univ, one_smul,
        (RandomizedPolicy.waiting n).integral_mixedClockResidual_zero P known hbound hz, sub_zero]

lemma Instance.mixedScalarValueMoment_one_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedScalarValueMoment known k z 1 ≤ optimalScalarValue P 1 z + 2 * P.mixedSuffixMoment known k z 1 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hVI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using mixedScalarValue_integrable_pow (k := k) P known hbound hz 1
  have hEI : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 1
  have hGI := hEI.integral_prod_left
  have h : (∫ a, optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k) ≤
      ∫ a, optimalScalarValue P 1 z + 2 * (∫ u,
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n)
        ∂P.trainingCoordinateLaw k := by
    apply integral_mono hVI ((integrable_const _).add (hGI.const_mul 2))
    intro a
    have h := (abs_le.mp ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).abs_value_difference_le_residualSuffix P
      (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) hP (by norm_num : (0 : ℝ) < 1) hz)).2
    simp only [Pi.add_apply] at *
    change optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ≤ optimalScalarValue P 1 z + 2 * (∫ u, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n)
    simp only [Instance.expectedResidualSuffixEnvelope] at h
    linarith
  rw [integral_add (f := fun _ => optimalScalarValue P 1 z)
      (g := fun a => 2 * (∫ u, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n))
      (integrable_const _) (hGI.const_mul 2), integral_const, probReal_univ, one_smul, integral_const_mul] at h
  have he : P.mixedSuffixMoment known k z 1 =
      ∫ a, (∫ u, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n)
        ∂P.trainingCoordinateLaw k := by
    simpa only [Instance.mixedSuffixMoment, pow_one] using integral_prod _ hEI
  rw [← he] at h
  simpa only [Instance.mixedScalarValueMoment, pow_one] using h

lemma Instance.mixedTruePremiumMoment_one_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedTruePremiumMoment known k z 1 ≤ optimalScalarValue P 1 z + 2 * Real.sqrt (P.mixedSuffixMoment known k z 2) := by
  have h1 := P.mixedTruePremiumMoment_one_eq_value (k := k) known hbound hz
  have h2 := P.mixedScalarValueMoment_one_le (k := k) known hbound hz
  have hI1 : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 1
  have hs : P.mixedSuffixMoment known k z 1 ≤ Real.sqrt (P.mixedSuffixMoment known k z 2) := by
    simpa only [Instance.mixedSuffixMoment, pow_one] using
      ProphetSecretary.Statistics.integral_le_sqrt_second _ hI1 (mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 2)
  linarith

/-- Jensen and the pointwise residual comparison control the reoptimized empirical
value's cubic moment at a fixed scalar. -/
theorem Instance.mixedScalarValueMoment_three_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedScalarValueMoment known k z 3 ≤ 4 * optimalScalarValue P 1 z ^ 3 + 32 * P.mixedSuffixMoment known k z 3 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hv : 0 ≤ optimalScalarValue P 1 z := optimalScalarValue_nonnegative P hP zero_le_one hz
  have hE1 : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 1
  have hE3 := mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 3
  have hV3 := mixedScalarValue_integrable_pow (k := k) P known hbound hz 3
  have hpoint : ∀ᵐ a ∂P.trainingCoordinateLaw k,
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ^ 3 ≤
        4 * optimalScalarValue P 1 z ^ 3 + 32 * (∫ u,
          (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n) := by
    filter_upwards [hE1.prod_right_ae, hE3.prod_right_ae] with a hI1 hI3
    let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
    let g := ∫ u, Q.residualSuffixEnvelope P 1 z u ∂Instance.clocksLaw n
    have hQ := mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known (reservoirCoordinates.symm a)
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
      (g := fun a => 32 * (∫ u, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n))
      (integrable_const _) (hE3.integral_prod_left.const_mul 32), integral_const, probReal_univ, one_smul, integral_const_mul] at h
  have he : P.mixedSuffixMoment known k z 3 =
      ∫ a, (∫ u, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 3 ∂Instance.clocksLaw n)
        ∂P.trainingCoordinateLaw k := integral_prod _ hE3
  rw [← he] at h
  exact h

/-- The true-law premium cubic moment is controlled by the true value and the
square root of the sixth suffix moment, with explicit constants. -/
theorem Instance.mixedTruePremiumMoment_three_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedTruePremiumMoment known k z 3 ≤ 208 * optimalScalarValue P 1 z ^ 3 +
      1668 * Real.sqrt (P.mixedSuffixMoment known k z 6) := by
  have hU3 := mixedTruePremium_joint_integrable_pow (k := k) P known hbound hz 3
  have hH3 := mixedDesignPremium_joint_integrable_pow (k := k) P known hbound hz 3
  have hE3 := mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 3
  have hE6 := mixedSuffix_joint_integrable_pow (k := k) P known hbound hz 6
  have hraw : P.mixedTruePremiumMoment known k z 3 ≤ 4 * P.mixedDesignPremiumMoment known k z 3 +
      4 * P.mixedSuffixMoment known k z 3 := by
    have h : (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2 ^ 3
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        ∫ v, 4 * (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremium 1 z v.2 ^ 3 +
          4 * (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ^ 3
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
      apply integral_mono hU3 ((hH3.const_mul 4).add (hE3.const_mul 4))
      intro v
      let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)
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
  have hKac := P.mixedDesignPremiumMoment_three_le (k := k) known hbound hz
  have hVal := P.mixedScalarValueMoment_three_le (k := k) known hbound hz
  have hRoot : P.mixedSuffixMoment known k z 3 ≤ Real.sqrt (P.mixedSuffixMoment known k z 6) := by
    simpa only [Instance.mixedSuffixMoment] using
      ProphetSecretary.Statistics.integral_cube_le_sqrt_sixth _ hE3 hE6
  nlinarith

end ProphetSecretary.Model
