import ProphetSecretary.Limiting.CountableWeightEnvelope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Reward and duration at a normalized critical instance

At positive weights summing to one and prophet mean one, criticality gives
scalar value C. Its scalar-weight derivative vanishes at the interior minimum
of the nonnegative gap. The actual canonical optimizer therefore has both
expected reward and expected duration equal to C.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem critical_canonical_reward_duration (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hMean : B.expectedMaximum=1)
    (hCritical : B.IsCritical w c) :
    (B.valuePolicy hw hc).expectedReward=optimalCompetitiveRatio ∧
      (B.valuePolicy hw hc).expectedDuration=optimalCompetitiveRatio := by
  have hZero := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hValue : B.optimalScalarValue w c=optimalCompetitiveRatio := by
    have h := hCritical.2
    unfold scalarGap at h
    rw [hMean,mul_one,hSum,mul_one] at h
    exact sub_eq_zero.mp h
  let f := fun θ : ℝ => B.optimalScalarValue (w+θ) (c-θ)-optimalCompetitiveRatio
  have hfZero : f 0=0 := by simp only [f,add_zero,sub_zero,hValue,sub_self]
  have hRadius : 0<min w c := lt_min hw hc
  have hMin : IsLocalMin f 0 := by
    change ∀ᶠ θ in 𝓝 (0 : ℝ), f 0≤f θ
    rw [hfZero]
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hRadius) hRadius] with θ hθ
    have hwθ : 0≤w+θ := by linarith only [hθ.1,min_le_left w c]
    have hcθ : 0≤c-θ := by linarith only [hθ.2,min_le_right w c]
    have hDen : (w+θ)*B.expectedMaximum+(c-θ)=1 := by rw [hMean,mul_one];linarith only [hSum]
    have h := B.scalarGap_nonnegative hwθ hcθ
    unfold scalarGap at h
    rw [hDen,mul_one] at h
    exact h
  have hDeriv := (B.hasDerivAt_optimalScalarValue_weight hZero hw hc).sub_const optimalCompetitiveRatio
  have hSlope : (B.valuePolicy hw hc).expectedWeightSlope=0 := hMin.hasDerivAt_eq_zero hDeriv
  have hRT : (B.valuePolicy hw hc).expectedReward=(B.valuePolicy hw hc).expectedDuration := sub_eq_zero.mp hSlope
  have hScalar : (B.valuePolicy hw hc).scalarObjective w c=(B.valuePolicy hw hc).expectedReward := by
    unfold RandomizedCountablePolicy.scalarObjective
    rw [←hRT,←add_mul,hSum,one_mul]
  have hReward : (B.valuePolicy hw hc).expectedReward=optimalCompetitiveRatio :=
    hScalar.symm.trans ((B.valuePolicy_optimal hZero hw hc).trans hValue)
  exact ⟨hReward,hRT.symm.trans hReward⟩

end ProphetSecretary.Limiting.CountableInstance
