import ProphetSecretary.Analysis.EmpiricalLossRates
import ProphetSecretary.Analysis.MomentTailBound

/-!
# Averaging the near-threshold time loss

The time integral is dominated by CBE²/x. Its actual weighted second moment
at entrance a=Ax yields an explicit multiple of (1+S)x/k. The multiplier B
and error may be dependent; the premise is their joint moment.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Analysis

lemma integral_nonnegative_le_scaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F W : Ω → ℝ} (hm : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hW : Integrable W μ) {C : ℝ} (hdom : ∀ᵐ ω ∂μ, F ω ≤ C * W ω) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤ C * ∫ ω, W ω ∂μ := by
  have hi : Integrable F μ := (hW.const_mul C).mono' hm (by
    filter_upwards [hF0, hdom] with ω h0 hd
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hd)
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi (hW.const_mul C) hdom
  rwa [integral_const_mul] at h

/-- Input W is the weighted squared entrance error B E². All rate constants
are explicit and independent of the number of variables. -/
theorem empirical_expected_near_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F W : Ω → ℝ} (hm : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hW : Integrable W μ) {k x A C C₂ S hi : ℝ}
    (hk : 0 < k) (hxk : 1 / k ≤ x) (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hS : 0 ≤ S) (hhi : 0 < hi)
    (hdom : ∀ᵐ ω ∂μ, F ω ≤ (C / x) * W ω)
    (hmoment : (∫ ω, W ω ∂μ) ≤ C₂ * (A * x / k + 1 / k ^ 2) * (A * x * (1 + S) / hi)) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤
      (C * C₂ * A * (A + 1) / hi) * (1 + S) * x / k := by
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have hbase := integral_nonnegative_le_scaled μ hm hF0 hW hdom
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hmom := mul_le_mul_of_nonneg_left hmoment (div_nonneg hC hx.le)
  have heq : (C / x) * (C₂ * (A * x / k + 1 / k ^ 2) * (A * x * (1 + S) / hi)) =
      ((C * C₂ / hi) * (1 + S)) * ((A * x / k + 1 / k ^ 2) * A) := by
    field_simp
  rw [heq] at hmom
  have hrate := mul_le_mul_of_nonneg_left (empirical_near_rate_le hk hxk hA)
    (by positivity : 0 ≤ (C * C₂ / hi) * (1 + S))
  have hfinal := hmom.trans hrate
  have heq' : ((C * C₂ / hi) * (1 + S)) * (A * (A + 1) * x / k) =
      (C * C₂ * A * (A + 1) / hi) * (1 + S) * x / k := by ring
  exact hfinal.trans_eq heq'

end ProphetSecretary.Analysis
