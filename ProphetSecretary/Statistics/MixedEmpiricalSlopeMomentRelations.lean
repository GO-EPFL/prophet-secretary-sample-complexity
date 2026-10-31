import ProphetSecretary.Statistics.MixedEmpiricalSlopeJointMoments

/-!
# Closing mixed scalar-increment premium moments

The true normalized premium differs from its design counterpart by the complete
centered mixed residual difference. Actual Kac and Cauchy–Schwarz estimates
close its cubic budget using the sixth mixed suffix moment.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedTrueSlopePremiumSum_eq_design_sub_full (P : Instance n) (known : Finset (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    mixedTrueSlopePremiumSum P known z z' u a =
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).premiumSlopeSum z z' u -
      ProphetSecretary.Statistics.suffixSum u (fun i =>
        ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i -
         (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z' u i) / (z' - z)) none := by
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
  rw [mixedTrueSlopePremiumSum, Q.unstoppedPremiumUnder_eq_difference P 1 z u,
    Q.unstoppedPremiumUnder_eq_difference P 1 z' u,
    ProphetSecretary.Statistics.suffixSum_sub_div]
  simp only [Instance.premiumSlopeSum, ProphetSecretary.Statistics.suffixSum]
  ring

lemma Instance.mixedSlopeTruePremiumMoment_nonnegative (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (p : ℕ) :
    0 ≤ P.mixedSlopeTruePremiumMoment known k z z' p := by
  apply integral_nonneg_of_ae
  have hv : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (Instance.clocksLaw n) := measurePreserving_snd
  filter_upwards [hv.quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n := n))] with v hv
  exact pow_nonneg (mixedTrueSlopePremiumSum_bounds P (P.integrable_maximum_of_bounded hbound) known hz hzz
    v.2 (fun i => (hv i).1) v.1).1 p

/-- Uniform true-premium cubic localization for the normalized increment. -/
theorem Instance.mixedSlopeTruePremiumMoment_three_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeTruePremiumMoment known k z z' 3 ≤
      52 + 4 * Real.sqrt (P.mixedSlopeSuffixMoment known k z z' 6) := by
  have hU3 := mixedTrueSlopePremium_joint_integrable_pow (k := k) P known hbound hz hzz 3
  have hH3 := mixedSlopeDesignPremium_joint_integrable_pow (k := k) P known hbound hz hzz 3
  have hE3 := mixedSlopeSuffix_joint_integrable_pow (k := k) P known hbound hz hzz 3
  have hE6 := mixedSlopeSuffix_joint_integrable_pow (k := k) P known hbound hz hzz 6
  have hv : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (Instance.clocksLaw n) := measurePreserving_snd
  have hraw : P.mixedSlopeTruePremiumMoment known k z z' 3 ≤
      4 * P.mixedSlopeDesignPremiumMoment known k z z' 3 + 4 * P.mixedSlopeSuffixMoment known k z z' 3 := by
    have h := integral_mono_ae hU3 ((hH3.const_mul 4).add (hE3.const_mul 4)) (by
      filter_upwards [hv.quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n := n))] with v hv
      let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)
      have hhat := Q.premiumSlopeSum_bounds (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) hz hzz v.2 hv
      have htrue := mixedTrueSlopePremiumSum_bounds P (P.integrable_maximum_of_bounded hbound) known
        hz hzz v.2 (fun i => (hv i).1) v.1
      have hrel := mixedTrueSlopePremiumSum_eq_design_sub_full P known z z' v.2 v.1
      have hfull : |ProphetSecretary.Statistics.suffixSum v.2 (fun i =>
          (Q.transitionResidual P 1 z v.2 i - Q.transitionResidual P 1 z' v.2 i) / (z' - z)) none| ≤
          Q.residualSlopeSuffixEnvelope P z z' v.2 := ProphetSecretary.Statistics.le_suffixEnvelope _ _ none
      have hle : mixedTrueSlopePremiumSum P known z z' v.2 v.1 ≤
          Q.premiumSlopeSum z z' v.2 + Q.residualSlopeSuffixEnvelope P z z' v.2 := by
        have h := (abs_le.mp hfull).1
        linarith
      have hp := pow_le_pow_left₀ htrue.1 hle 3
      have hEnv0 : 0 ≤ Q.residualSlopeSuffixEnvelope P z z' v.2 := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
      have hadd := ProphetSecretary.Statistics.cube_add_le_four_cubes hhat.1 hEnv0
      exact hp.trans hadd)
    simp only [Pi.add_apply] at h
    have he := integral_add (hH3.const_mul 4) (hE3.const_mul 4)
    rw [he, integral_const_mul, integral_const_mul] at h
    exact h
  have hKac := P.mixedSlopeDesignPremiumMoment_three_le (k := k) known hbound hz hzz
  have hRoot : P.mixedSlopeSuffixMoment known k z z' 3 ≤ Real.sqrt (P.mixedSlopeSuffixMoment known k z z' 6) := by
    simpa only [Instance.mixedSlopeSuffixMoment] using
      ProphetSecretary.Statistics.integral_cube_le_sqrt_sixth _ hE3 hE6
  linarith

end ProphetSecretary.Model
