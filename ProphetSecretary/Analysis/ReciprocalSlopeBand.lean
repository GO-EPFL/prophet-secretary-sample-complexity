import ProphetSecretary.Analysis.ThresholdBand

/-!
# Disagreement bands under a reciprocal slope estimate

The reciprocal estimate x(s−t)≤CB(g(s)−g(t)) is allowed only on the selected
band domain S. It permits jumps and B=0. The resulting local-loss integral
is at most 2CB E²/x, as needed for the near region in `upstat:selected`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace ProphetSecretary.Analysis

lemma reciprocalSlope_band_diameter {S : Set ℝ} {g : ℝ → ℝ} {x C B E : ℝ}
    (hx : 0 < x) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hslope : ∀ t ∈ S, ∀ s ∈ S, t ≤ s → x * (s - t) ≤ C * B * (g s - g t))
    {t s : ℝ} (ht : t ∈ S ∩ {u | |g u| ≤ E}) (hs : s ∈ S ∩ {u | |g u| ≤ E}) :
    dist t s ≤ 2 * C * B * E / x := by
  have hcb : 0 ≤ C * B := mul_nonneg hC hB
  have hgt := abs_le.mp (show |g t| ≤ E from ht.2)
  have hgs := abs_le.mp (show |g s| ≤ E from hs.2)
  rcases le_total t s with hts | hst
  · have h := hslope t ht.1 s hs.1 hts
    have hg : g s - g t ≤ 2 * E := by linarith only [hgt.1, hgs.2]
    have hm := mul_le_mul_of_nonneg_left hg hcb
    have hd : s - t ≤ 2 * C * B * E / x := by
      apply (le_div_iff₀ hx).mpr
      nlinarith only [h, hm]
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hd
  · have h := hslope s hs.1 t ht.1 hst
    have hg : g t - g s ≤ 2 * E := by linarith only [hgs.1, hgt.2]
    have hm := mul_le_mul_of_nonneg_left hg hcb
    have hd : t - s ≤ 2 * C * B * E / x := by
      apply (le_div_iff₀ hx).mpr
      nlinarith only [h, hm]
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)] using hd

theorem volume_reciprocalSlope_band_le {S : Set ℝ} {g : ℝ → ℝ} {x C B E : ℝ}
    (hx : 0 < x) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hslope : ∀ t ∈ S, ∀ s ∈ S, t ≤ s → x * (s - t) ≤ C * B * (g s - g t)) :
    volume (S ∩ {u | |g u| ≤ E}) ≤ ENNReal.ofReal (2 * C * B * E / x) :=
  (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le fun _ ht _ hs =>
    reciprocalSlope_band_diameter hx hC hB hslope ht hs)

/-- The expectation over training is taken later; here E and B are held fixed
throughout the candidate-time integral, including for a training-selected scalar. -/
theorem integral_reciprocalSlope_loss_le {S : Set ℝ} (hS : MeasurableSet S)
    (hS01 : S ⊆ Icc (0 : ℝ) 1) {g loss : ℝ → ℝ} {x C B E : ℝ}
    (hx : 0 < x) (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E) (hg : Measurable g)
    (hslope : ∀ t ∈ S, ∀ s ∈ S, t ≤ s → x * (s - t) ≤ C * B * (g s - g t))
    (hm : AEStronglyMeasurable loss (volume.restrict S))
    (h0 : ∀ᵐ t ∂volume.restrict S, 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict S, loss t ≤ (S ∩ {u | |g u| ≤ E}).indicator (fun _ => E) t) :
    (∫ t in S, loss t) ≤ 2 * C * B * E ^ 2 / x := by
  let T := S ∩ {u | |g u| ≤ E}
  have hT : MeasurableSet T := hS.inter (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)
  have hfinite : volume S < ⊤ := (measure_mono hS01).trans_lt (by simp [Real.volume_Icc])
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hfinite⟩
  have hb : ∀ᵐ t ∂volume.restrict S, ‖loss t‖ ≤ E := by
    filter_upwards [h0, hdom] with t ht hd
    rw [Real.norm_eq_abs, abs_of_nonneg ht]
    exact hd.trans (by by_cases h : t ∈ T <;> simp [T, h, hE])
  have hi : Integrable loss (volume.restrict S) := Integrable.of_bound hm E hb
  have hdomI : Integrable (T.indicator (fun _ => E)) (volume.restrict S) := (integrable_const E).indicator hT
  have hint := integral_mono_ae hi hdomI hdom
  rw [integral_indicator_const E hT] at hint
  have htmeasure : (volume.restrict S).real T = volume.real T := by
    change ((volume.restrict S) T).toReal = (volume T).toReal
    rw [Measure.restrict_apply hT, inter_eq_left.mpr inter_subset_left]
  rw [htmeasure, smul_eq_mul] at hint
  have hvol : volume.real T ≤ 2 * C * B * E / x :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (volume_reciprocalSlope_band_le (E := E) hx hC hB hslope)
  have hprod := mul_le_mul_of_nonneg_right hvol hE
  have heq : (2 * C * B * E / x) * E = 2 * C * B * E ^ 2 / x := by ring
  exact hint.trans (hprod.trans_eq heq)

end ProphetSecretary.Analysis
