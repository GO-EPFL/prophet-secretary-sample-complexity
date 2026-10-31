import ProphetSecretary.Analysis.MovingRoot
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A triangular primitive with a moving center

Both the function and its zero may vary. Uniform Lipschitz control dominates the
rescaled integrals; continuity of the horizon derivative identifies their limit.
Oriented affine substitutions handle both directions of the root displacement.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Analysis

theorem tendsto_moving_primitive_quotient {F T : ℝ → ℝ → ℝ} {r : ℝ → ℝ}
    {p d A B a b D : ℝ} {L : ℝ≥0}
    (hp : p ∈ Ioo A B) (hd : d ∈ Ioo a b) (hr0 : r p = d) (hR : HasDerivAt r D p)
    (hLip : ∀ q ∈ Ioo A B, LipschitzWith L (F q))
    (hD : ∀ q ∈ Ioo A B, ∀ z ∈ Ioo a b, HasDerivAt (F q) (T q z) z)
    (hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (p, d)) :
    Tendsto (fun h : ℝ ↦ (∫ s in r (p + h)..d, F (p + h) s - F (p + h) (r (p + h))) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (T p d * D ^ 2 / 2)) := by
  let root : ℝ → ℝ := fun h ↦ r (p + h)
  let Δ : ℝ → ℝ := fun h ↦ d - root h
  let G : ℝ → ℝ → ℝ := fun h v ↦
    (F (p + h) (root h + Δ h * v) - F (p + h) (root h)) / h
  have hAdd : Tendsto (fun h : ℝ ↦ p + h) (𝓝 0) (𝓝 p) := by
    have hc : Continuous (fun h : ℝ ↦ p + h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto 0
  have hr : Tendsto r (𝓝 p) (𝓝 d) := by simpa only [hr0] using hR.continuousAt.tendsto
  have hRatio : Tendsto (fun h : ℝ ↦ Δ h / h) (𝓝[≠] 0) (𝓝 (-D)) := by
    convert hR.tendsto_slope_zero.neg using 1
    funext h
    dsimp only [Δ, root]
    rw [hr0, smul_eq_mul]
    ring
  have hInside : ∀ᶠ h : ℝ in 𝓝 0, p + h ∈ Ioo A B := hAdd (Ioo_mem_nhds hp.1 hp.2)
  have hPointwise (v : ℝ) : Tendsto (fun h : ℝ ↦ G h v) (𝓝[≠] 0) (𝓝 (T p d * (-D) * v)) := by
    let s : ℝ → ℝ := fun q ↦ r q + (d - r q) * v
    have hs : Tendsto s (𝓝 p) (𝓝 d) := by
      have hConst : Tendsto (fun _ : ℝ ↦ d) (𝓝 p) (𝓝 d) := tendsto_const_nhds
      simpa only [s, sub_self, zero_mul, add_zero] using hr.add ((hConst.sub hr).mul_const v)
    have hQ := (tendsto_betweenSecant hp hd hr hs hD hT).comp hAdd
    have hProd := ((hQ.mono_left nhdsWithin_le_nhds).mul hRatio).mul_const v
    apply hProd.congr'
    exact Filter.Eventually.of_forall (fun h ↦ by
      have hm := betweenSecant_mul_sub F T r s (p + h)
      have hInc : s (p + h) - r (p + h) = (d - r (p + h)) * v := by dsimp only [s]; ring
      rw [hInc] at hm
      change betweenSecant F T r s (p + h) * ((d - r (p + h)) / h) * v =
        (F (p + h) (s (p + h)) - F (p + h) (r (p + h))) / h
      rw [← hm]
      ring)
  have hRatioBound : ∀ᶠ h : ℝ in 𝓝[≠] 0, |Δ h / h| ≤ |D| + 1 := by
    filter_upwards [hRatio (Metric.ball_mem_nhds (-D) zero_lt_one)] with h hh
    have ht := abs_sub_le (Δ h / h) (-D) 0
    simp only [sub_zero, abs_neg] at ht
    have hh' : |Δ h / h - (-D)| < 1 := hh
    linarith
  have hInt : Tendsto (fun h : ℝ ↦ ∫ v in (0 : ℝ)..1, G h v) (𝓝[≠] 0)
      (𝓝 (∫ v in (0 : ℝ)..1, T p d * (-D) * v)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ ↦ (L : ℝ) * (|D| + 1))
    · filter_upwards [hInside.filter_mono nhdsWithin_le_nhds] with h hh
      have hc : Continuous (G h) :=
        (((hLip (p + h) hh).continuous.comp
          (continuous_const.add (continuous_const.mul continuous_id))).sub continuous_const).div_const h
      exact hc.measurable.aestronglyMeasurable
    · filter_upwards [hInside.filter_mono nhdsWithin_le_nhds, hRatioBound] with h hh hB
      exact Filter.Eventually.of_forall (fun v hv ↦ by
        have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hv
        have habsv : |v| ≤ 1 := by rw [abs_of_pos hv'.1]; exact hv'.2
        have hl := (hLip (p + h) hh).dist_le_mul (root h + Δ h * v) (root h)
        simp only [Real.dist_eq, add_sub_cancel_left] at hl
        calc
          ‖G h v‖ = |F (p + h) (root h + Δ h * v) - F (p + h) (root h)| / |h| := by
            change ‖(F (p + h) (root h + Δ h * v) - F (p + h) (root h)) / h‖ = _
            rw [Real.norm_eq_abs, abs_div]
          _ ≤ ((L : ℝ) * |Δ h * v|) / |h| := div_le_div_of_nonneg_right hl (abs_nonneg h)
          _ = (L : ℝ) * |Δ h / h| * |v| := by rw [abs_mul, abs_div]; ring
          _ ≤ ((L : ℝ) * (|D| + 1)) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB L.coe_nonneg) habsv (abs_nonneg _) (by positivity)
          _ = _ := mul_one _)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun v _ ↦ hPointwise v)
  have hIntValue : (∫ v in (0 : ℝ)..1, T p d * (-D) * v) = T p d * (-D) / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hIntValue] at hInt
  have hProduct := hRatio.mul hInt
  have hCoeff : (-D) * (T p d * (-D) / 2) = T p d * D ^ 2 / 2 := by ring
  rw [hCoeff] at hProduct
  apply hProduct.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hh
  have ha := intervalIntegral.smul_integral_comp_add_mul (f := fun s ↦ F (p + h) s - F (p + h) (root h))
    (a := (0 : ℝ)) (b := 1) (Δ h) (root h)
  simp only [smul_eq_mul, mul_zero, mul_one, add_zero] at ha
  have hEnd : root h + Δ h = d := by dsimp only [Δ]; ring
  rw [hEnd] at ha
  change (Δ h / h) * (∫ v in (0 : ℝ)..1, G h v) = _
  rw [← ha]
  dsimp only [G, root]
  rw [intervalIntegral.integral_div]
  field_simp [hne]

end ProphetSecretary.Analysis
