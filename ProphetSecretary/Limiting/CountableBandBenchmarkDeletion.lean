import ProphetSecretary.Limiting.CountableBandBenchmarkSecant
import ProphetSecretary.Limiting.CountableBandStationarity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Zero prophet intensity response permits deletion of the band

The bounded CDF secant controls a full deletion by an arbitrarily small
positive intensity increment. Its actual derivative limit is zero. Monotonicity
supplies the opposite inequality, proving benchmark equality separately from
any policy-value equality.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting.CountableInstance

theorem expectedMaximum_scaleBand_zero_eq_of_prophetDerivative_zero
    (B : CountableInstance) (hZero : B.terminal=0) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hScore : B.prophetBandLikelihoodDerivative S=0) :
    (B.scaleBand S 0).expectedMaximum=B.expectedMaximum := by
  have hd := B.hasDerivAt_expectedMaximum_bandLikelihoodPath hS hb hSub
  rw [hScore] at hd
  have hF0 : (B.bandLikelihoodPath S 0).expectedMaximum=B.expectedMaximum := by rw [B.bandLikelihoodPath_zero]
  let E := Real.exp (2*B.intensity.real S)
  have hLimit : Tendsto (fun h : ℝ => E*(((B.bandLikelihoodPath S h).expectedMaximum-B.expectedMaximum)/h))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := hd.tendsto_slope_zero_right.const_mul E
    simpa only [zero_add,hF0,smul_eq_mul,mul_zero,zero_mul,div_eq_mul_inv,mul_comm] using h
  have hSmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h<1/4 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/4))
  have hEvent : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      B.expectedMaximum-(B.scaleBand S 0).expectedMaximum≤
        E*(((B.bandLikelihoodPath S h).expectedMaximum-B.expectedMaximum)/h) := by
    filter_upwards [self_mem_nhdsWithin,hSmall] with h hh hQuarter
    have hh0 : 0<h := hh
    have hAbs : |h|≤1/4 := by rw [abs_of_pos hh0]; exact hQuarter.le
    let r : ℝ≥0 := ⟨1+h,by linarith only [hh0]⟩
    have hSecant := B.expectedMaximum_band_deletion_secant hZero hS hb hSub hh0
      (hQuarter.le.trans (by norm_num : (1/4 : ℝ)≤1)) (r := r) rfl
    have hPath : B.bandLikelihoodPath S h=B.scaleBand S r := B.bandLikelihoodPath_of_mem S hAbs
    rw [← hPath] at hSecant
    change h*(B.expectedMaximum-(B.scaleBand S 0).expectedMaximum)≤
      E*((B.bandLikelihoodPath S h).expectedMaximum-B.expectedMaximum) at hSecant
    have hDivide : B.expectedMaximum-(B.scaleBand S 0).expectedMaximum≤
        E*((B.bandLikelihoodPath S h).expectedMaximum-B.expectedMaximum)/h := by
      apply (le_div_iff₀ hh0).mpr
      nlinarith only [hSecant]
    exact hDivide.trans_eq (by rw [div_eq_mul_inv,div_eq_mul_inv]; ring)
  have hDifference : B.expectedMaximum-(B.scaleBand S 0).expectedMaximum≤0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hLimit hEvent
  have hOrder := B.expectedMaximum_scaleBand_order hZero hS (r := 0) (s := 1) (by norm_num)
  rw [B.scaleBand_one] at hOrder
  exact le_antisymm hOrder (sub_nonpos.mp hDifference)

theorem expectedMaximum_scaleBand_zero_eq_of_critical_scalarDerivative_zero
    (B : CountableInstance) {w c : ℝ} (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hScalar : (B.valuePolicy hw hc).scalarBandLikelihoodDerivative S w c=0) :
    (B.scaleBand S 0).expectedMaximum=B.expectedMaximum :=
  B.expectedMaximum_scaleBand_zero_eq_of_prophetDerivative_zero
    (B.terminal_eq_zero_of_critical hw hc.le hCritical) hS hb hSub
    (B.prophetBandLikelihoodDerivative_eq_zero_of_scalarDerivative_zero hw hc hCritical hS hb hSub hScalar)

end ProphetSecretary.Limiting.CountableInstance
