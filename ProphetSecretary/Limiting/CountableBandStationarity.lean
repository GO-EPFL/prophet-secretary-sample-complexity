import ProphetSecretary.Limiting.CountableBandEnvelope
import ProphetSecretary.Limiting.CountableBandMaximumDerivative
import ProphetSecretary.Limiting.NoReserve
import ProphetSecretary.Model.HalfGuarantee
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Critical stationarity under a finite-band intensity tilt

The scalar derivative uses a fixed base optimizer, whereas the prophet
response is the maximum's complete-count score correlation. Their equality
follows from the nonnegative actual scalar gap along the true perturbation.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem critical_band_likelihood_stationarity (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) :
    (B.valuePolicy hw hc).scalarBandLikelihoodDerivative S w c=
      optimalCompetitiveRatio*w*B.prophetBandLikelihoodDerivative S := by
  have hZero := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hBaseGap : (B.bandLikelihoodPath S 0).scalarGap w c=0 := by
    rw [B.bandLikelihoodPath_zero]
    exact hCritical.2
  have hMin : IsLocalMin (fun θ => (B.bandLikelihoodPath S θ).scalarGap w c) 0 := by
    change ∀ᶠ θ in 𝓝 (0 : ℝ), (B.bandLikelihoodPath S 0).scalarGap w c≤(B.bandLikelihoodPath S θ).scalarGap w c
    rw [hBaseGap]
    exact Eventually.of_forall (fun θ => (B.bandLikelihoodPath S θ).scalarGap_nonnegative hw.le hc.le)
  have hV := B.hasDerivAt_optimalScalarValue_bandLikelihoodPath hZero hw hc hS hb hSub
  have hM := B.hasDerivAt_expectedMaximum_bandLikelihoodPath hS hb hSub
  have hGap := hV.sub (((hM.const_mul w).add_const c).const_mul optimalCompetitiveRatio)
  have hStat := hMin.hasDerivAt_eq_zero hGap
  nlinarith only [hStat]

theorem prophetBandLikelihoodDerivative_eq_zero_of_scalarDerivative_zero
    (B : CountableInstance) {w c : ℝ} (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hScalar : (B.valuePolicy hw hc).scalarBandLikelihoodDerivative S w c=0) :
    B.prophetBandLikelihoodDerivative S=0 := by
  have h := B.critical_band_likelihood_stationarity hw hc hCritical hS hb hSub
  have hC : 0<optimalCompetitiveRatio := (by norm_num : (0 : ℝ)<1/2).trans_le half_le_optimalCompetitiveRatio
  rw [hScalar] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt (mul_pos hC hw))

end ProphetSecretary.Limiting.CountableInstance
