import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set

namespace ProphetSecretary.Reach

/-- The second-moment form of Jensen's inequality on a probability space. -/
theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun ω ↦ f ω ^ 2) μ) :
    (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  let m := ∫ ω, f ω ∂μ
  have h : 0 ≤ ∫ ω, (f ω - m) ^ 2 ∂μ :=
    integral_nonneg (fun ω ↦ sq_nonneg (f ω - m))
  have heq : (fun ω ↦ (f ω - m) ^ 2) =
      (fun ω ↦ (f ω ^ 2 - 2 * m * f ω) + m ^ 2) := by
    funext ω
    ring
  rw [heq, integral_add (f := fun ω ↦ f ω ^ 2 - 2 * m * f ω)
    (g := fun _ ↦ m ^ 2) (hf2.sub (hf.const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun ω ↦ f ω ^ 2) (g := fun ω ↦ 2 * m * f ω)
      hf2 (hf.const_mul (2 * m)), integral_const_mul, integral_const] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  dsimp [m] at h
  nlinarith

/-- Integrating an independent uniform clock up to a fixed pending duration. -/
theorem integral_min_clock {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t in (0 : ℝ)..1, min t s) = s - s ^ 2 / 2 := by
  have hc : Continuous (fun t : ℝ ↦ min t s) := continuous_id.min continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s 1)]
  have hl : (∫ t in (0 : ℝ)..s, min t s) = ∫ t in (0 : ℝ)..s, t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs0]
    intro t ht
    exact min_eq_left ht.2
  have hr : (∫ t in s..(1 : ℝ), min t s) = ∫ _t in s..(1 : ℝ), s := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs1]
    intro t ht
    exact min_eq_right ht.1
  rw [hl, hr, integral_id, intervalIntegral.integral_const]
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, smul_eq_mul]
  ring

/-- A density bounded by one and with total mass `A` on `[0,s]` has its smallest
first moment about `s` when all its mass occupies the final interval of length `A`.
This is the integral minimization in `lem:monotone-reach` / `upbound:strict-reach`. -/
theorem selection_duration_integral {s : ℝ} (hs : 0 ≤ s) {a : ℝ → ℝ}
    (ha : IntervalIntegrable a volume 0 s)
    (ha0 : ∀ t ∈ Icc 0 s, 0 ≤ a t)
    (ha1 : ∀ t ∈ Icc 0 s, a t ≤ 1) :
    (∫ t in (0 : ℝ)..s, a t) ^ 2 / 2 ≤
      ∫ t in (0 : ℝ)..s, (s - t) * a t := by
  let A := ∫ t in (0 : ℝ)..s, a t
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hs ha0
  have hAs : A ≤ s := by
    have h := intervalIntegral.integral_mono_on hs ha intervalIntegrable_const ha1
    simpa using h
  let b := s - A
  have hb0 : 0 ≤ b := sub_nonneg.mpr hAs
  have hbs : b ≤ s := sub_le_self s hA0
  have haL : IntervalIntegrable a volume 0 b :=
    ha.mono_set (by simpa only [uIcc_of_le hs, uIcc_of_le hb0] using Icc_subset_Icc le_rfl hbs)
  have haR : IntervalIntegrable a volume b s :=
    ha.mono_set (by simpa only [uIcc_of_le hs, uIcc_of_le hbs] using Icc_subset_Icc hb0 le_rfl)
  have hc (x y : ℝ) : IntervalIntegrable (fun t : ℝ ↦ b - t) volume x y :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have hpL : IntervalIntegrable (fun t ↦ (b - t) * a t) volume 0 b :=
    haL.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hpR : IntervalIntegrable (fun t ↦ (b - t) * a t) volume b s :=
    haR.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hleft : 0 ≤ ∫ t in (0 : ℝ)..b, (b - t) * a t := by
    apply intervalIntegral.integral_nonneg hb0
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr ht.2) (ha0 t ⟨ht.1, ht.2.trans hbs⟩)
  have hright : (∫ t in b..s, b - t) ≤ ∫ t in b..s, (b - t) * a t := by
    apply intervalIntegral.integral_mono_on hbs (hc b s) hpR
    intro t ht
    have hcoeff : b - t ≤ 0 := sub_nonpos.mpr ht.1
    have hab := ha1 t ⟨hb0.trans ht.1, ht.2⟩
    nlinarith
  have hlin : (∫ t in b..s, b - t) = -(A ^ 2 / 2) := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ ↦ b) (g := fun t : ℝ ↦ t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    dsimp [b]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hpL hpR
  have hbound : -(A ^ 2 / 2) ≤ ∫ t in (0 : ℝ)..s, (b - t) * a t := by
    rw [← hsplit]
    linarith
  have hdecomp : (∫ t in (0 : ℝ)..s, (b - t) * a t) =
      (∫ t in (0 : ℝ)..s, (s - t) * a t) - A * A := by
    have heq : (fun t ↦ (b - t) * a t) =
        (fun t ↦ (s - t) * a t - A * a t) := by
      funext t
      dsimp [b]
      ring
    rw [heq, intervalIntegral.integral_sub
      (f := fun t ↦ (s - t) * a t) (g := fun t ↦ A * a t)
      (ha.continuousOn_mul (continuous_const.sub continuous_id).continuousOn)
      (ha.const_mul A), intervalIntegral.integral_const_mul]
  rw [hdecomp] at hbound
  change A ^ 2 / 2 ≤ _
  nlinarith

/-- Averaging the conditional integral minimization and then applying Jensen.
The two outer integrability conditions are explicit; this lemma supplies the
analytic quadratic step rather than constructing a stopping policy. -/
theorem averaged_selection_duration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ : Ω → ℝ} {a : Ω → ℝ → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (hσ1 : ∀ ω, σ ω ≤ 1)
    (ha : ∀ ω, IntervalIntegrable (a ω) volume 0 (σ ω))
    (ha0 : ∀ ω t, t ∈ Icc 0 (σ ω) → 0 ≤ a ω t)
    (ha1 : ∀ ω t, t ∈ Icc 0 (σ ω) → a ω t ≤ 1)
    (hA : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..σ ω, a ω t) μ)
    (hB : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..σ ω, (σ ω - t) * a ω t) μ) :
    (∫ ω, (∫ t in (0 : ℝ)..σ ω, a ω t) ∂μ) ^ 2 / 2 ≤
      ∫ ω, (∫ t in (0 : ℝ)..σ ω, (σ ω - t) * a ω t) ∂μ := by
  let A := fun ω ↦ ∫ t in (0 : ℝ)..σ ω, a ω t
  have hAbounds : ∀ ω, 0 ≤ A ω ∧ A ω ≤ 1 := by
    intro ω
    constructor
    · exact intervalIntegral.integral_nonneg (hσ0 ω) (ha0 ω)
    · have h := intervalIntegral.integral_mono_on (hσ0 ω) (ha ω)
        intervalIntegrable_const (ha1 ω)
      simpa using h.trans (by simpa using hσ1 ω)
  have hA2 : Integrable (fun ω ↦ A ω ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hA.aestronglyMeasurable.pow 2)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change A ω ^ 2 ≤ 1
    nlinarith [(hAbounds ω).1, (hAbounds ω).2]
  have hJ := sq_integral_le_integral_sq μ hA hA2
  have hmin : ∀ ω, A ω ^ 2 / 2 ≤
      ∫ t in (0 : ℝ)..σ ω, (σ ω - t) * a ω t := by
    intro ω
    exact selection_duration_integral (hσ0 ω) (ha ω) (ha0 ω) (ha1 ω)
  have hbound := integral_mono (hA2.div_const 2) hB hmin
  rw [integral_div] at hbound
  exact (div_le_div_of_nonneg_right hJ (by norm_num)).trans hbound

/-- The universal (non-monotone-policy) reach estimate after conditioning on
all randomness except the independent uniform candidate clock. Its hypotheses
are the pathwise lower comparison and the explicit integration obligations. -/
theorem mean_pending_le_twice_mean_duration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {σ : Ω → ℝ} {τ : Ω → ℝ → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (hσ1 : ∀ ω, σ ω ≤ 1)
    (hσ : Integrable σ μ)
    (hτI : ∀ ω, IntervalIntegrable (τ ω) volume 0 1)
    (hT : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..1, τ ω t) μ)
    (hmin : ∀ ω t, t ∈ Icc 0 1 → min t (σ ω) ≤ τ ω t) :
    (∫ ω, σ ω ∂μ) ≤ 2 * ∫ ω, (∫ t in (0 : ℝ)..1, τ ω t) ∂μ := by
  have hpoint : ∀ ω, σ ω / 2 ≤ ∫ t in (0 : ℝ)..1, τ ω t := by
    intro ω
    have hc : Continuous (fun t : ℝ ↦ min t (σ ω)) :=
      continuous_id.min continuous_const
    have h := intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1)
      (hc.intervalIntegrable 0 1) (hτI ω) (hmin ω)
    rw [integral_min_clock (hσ0 ω) (hσ1 ω)] at h
    nlinarith [hσ0 ω, hσ1 ω, mul_nonneg (hσ0 ω) (sub_nonneg.mpr (hσ1 ω))]
  have hbound := integral_mono (hσ.div_const 2) hT hpoint
  rw [integral_div] at hbound
  linarith


/-- The probability that a unit uniform clock arrives before a fixed pending
duration is that duration itself. Endpoints have no Lebesgue mass. -/
theorem integral_reach_clock {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t in (0 : ℝ)..1, if t ≤ s then (1 : ℝ) else 0) = s := by
  classical
  have hm : Measurable (fun t : ℝ ↦ if t ≤ s then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hInt : IntegrableOn (fun t : ℝ ↦ if t ≤ s then (1 : ℝ) else 0) (Icc 0 1) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with t
    split_ifs <;> norm_num
  have hI : IntervalIntegrable (fun t : ℝ ↦ if t ≤ s then (1 : ℝ) else 0) volume 0 1 :=
    (show IntegrableOn (fun t : ℝ ↦ if t ≤ s then (1 : ℝ) else 0) (uIcc 0 1)
      from by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hInt).intervalIntegrable
  have hL : IntervalIntegrable (fun t : ℝ ↦ if t ≤ s then (1 : ℝ) else 0) volume 0 s :=
    hI.mono_set (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), uIcc_of_le hs0] using Icc_subset_Icc le_rfl hs1)
  have hR : IntervalIntegrable (fun t : ℝ ↦ if t ≤ s then (1 : ℝ) else 0) volume s 1 :=
    hI.mono_set (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), uIcc_of_le hs1] using Icc_subset_Icc hs0 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR]
  have hl : (∫ t in (0 : ℝ)..s, if t ≤ s then (1 : ℝ) else 0) = s := by
    calc
      _ = ∫ _t in (0 : ℝ)..s, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hs0]
        intro t ht
        simp only [if_pos ht.2]
      _ = s := by simp
  have hr : (∫ t in s..(1 : ℝ), if t ≤ s then (1 : ℝ) else 0) = 0 := by
    calc
      _ = ∫ _t in s..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs1
        intro t ht
        simp only [if_neg (not_le.mpr ht.1)]
      _ = 0 := by simp
  rw [hl, hr, add_zero]

/-- Conditioning on the residual coordinate proves the reach identity under
an independent uniform clock. -/
theorem integral_reach_clock_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ : Ω → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (hσ1 : ∀ ω, σ ω ≤ 1)
    (hreach : Integrable (fun z : Ω × ℝ ↦ if z.2 ≤ σ z.1 then (1 : ℝ) else 0)
      (μ.prod (volume.restrict (Icc 0 1)))) :
    (∫ z, (if z.2 ≤ σ z.1 then (1 : ℝ) else 0)
      ∂μ.prod (volume.restrict (Icc 0 1))) = ∫ ω, σ ω ∂μ := by
  classical
  rw [integral_prod _ hreach]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact integral_reach_clock (hσ0 ω) (hσ1 ω)

/-- Fubini for an independent uniform candidate clock. The residual space may
include all other offers, clocks, training data, and the policy seed. -/
theorem integral_min_clock_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ : Ω → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (hσ1 : ∀ ω, σ ω ≤ 1)
    (hmin : Integrable (fun z : Ω × ℝ ↦ min z.2 (σ z.1))
      (μ.prod (volume.restrict (Icc 0 1)))) :
    (∫ z, min z.2 (σ z.1) ∂μ.prod (volume.restrict (Icc 0 1))) =
      ∫ ω, (σ ω - σ ω ^ 2 / 2) ∂μ := by
  rw [integral_prod _ hmin]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact integral_min_clock (hσ0 ω) (hσ1 ω)

/-- The universal reach comparison on a genuine product probability space;
the independence used here is supplied by the product measure, and no pending
execution or its independence is postulated by this analytic lemma. -/
theorem pending_le_twice_duration_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ : Ω → ℝ} {τ : Ω × ℝ → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (hσ1 : ∀ ω, σ ω ≤ 1)
    (hσ : Integrable σ μ)
    (hτI : ∀ ω, IntervalIntegrable (fun t ↦ τ (ω, t)) volume 0 1)
    (hτ : Integrable τ (μ.prod (volume.restrict (Icc 0 1))))
    (hmin : ∀ ω t, t ∈ Icc 0 1 → min t (σ ω) ≤ τ (ω, t)) :
    (∫ ω, σ ω ∂μ) ≤
      2 * ∫ z, τ z ∂μ.prod (volume.restrict (Icc 0 1)) := by
  have hT : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..1, τ (ω, t)) μ := by
    simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using hτ.integral_prod_left
  have h := mean_pending_le_twice_mean_duration μ hσ0 hσ1 hσ hτI hT hmin
  rw [integral_prod _ hτ]
  simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using h

/-- An integrand that vanishes strictly after `s` can be integrated to `s`
instead of to the end of the unit clock interval. -/
theorem integral_until_eq_full {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hzero : ∀ t ∈ Ioo s 1, f t = 0) :
    (∫ t in (0 : ℝ)..s, f t) = ∫ t in (0 : ℝ)..1, f t := by
  have hL : IntervalIntegrable f volume 0 s :=
    hf.mono_set (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), uIcc_of_le hs0] using Icc_subset_Icc le_rfl hs1)
  have hR : IntervalIntegrable f volume s 1 :=
    hf.mono_set (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), uIcc_of_le hs1] using Icc_subset_Icc hs0 le_rfl)
  have hz : (∫ t in s..(1 : ℝ), f t) = 0 := by
    calc
      _ = ∫ _t in s..(1 : ℝ), (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le hs1 hzero
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hL hR
  simpa only [hz, add_zero] using hsplit

/-- The strict quadratic comparison after the pending execution has supplied
the pathwise gap bound. A selection density may be randomized and take any
value in `[0,1]`; its support must lie before the pending execution stops.
All outer integrability obligations are stated for the actual product law. -/
theorem quadratic_gap_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : Ω → ℝ} {τ a : Ω × ℝ → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (hσ1 : ∀ ω, σ ω ≤ 1)
    (hσ : Integrable σ μ)
    (haI : ∀ ω, IntervalIntegrable (fun t ↦ a (ω, t)) volume 0 1)
    (hτI : ∀ ω, IntervalIntegrable (fun t ↦ τ (ω, t)) volume 0 1)
    (ha : Integrable a (μ.prod (volume.restrict (Icc 0 1))))
    (hτ : Integrable τ (μ.prod (volume.restrict (Icc 0 1))))
    (hW : Integrable (fun z ↦ (σ z.1 - z.2) * a z)
      (μ.prod (volume.restrict (Icc 0 1))))
    (ha0 : ∀ ω t, t ∈ Icc 0 1 → 0 ≤ a (ω, t))
    (ha1 : ∀ ω t, t ∈ Icc 0 1 → a (ω, t) ≤ 1)
    (hsupport : ∀ ω t, σ ω < t → t < 1 → a (ω, t) = 0)
    (hgap : ∀ ω t, t ∈ Icc 0 1 →
      (σ ω - t) * a (ω, t) ≤ σ ω - τ (ω, t)) :
    (∫ z, a z ∂μ.prod (volume.restrict (Icc 0 1))) ^ 2 / 2 ≤
      (∫ ω, σ ω ∂μ) - ∫ z, τ z ∂μ.prod (volume.restrict (Icc 0 1)) := by
  have hAe : ∀ ω, (∫ t in (0 : ℝ)..σ ω, a (ω, t)) =
      ∫ t in (0 : ℝ)..1, a (ω, t) := by
    intro ω
    apply integral_until_eq_full (hσ0 ω) (hσ1 ω) (haI ω)
    exact fun t ht ↦ hsupport ω t ht.1 ht.2
  have hWI : ∀ ω, IntervalIntegrable (fun t ↦ (σ ω - t) * a (ω, t)) volume 0 1 :=
    fun ω ↦ (haI ω).continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hBe : ∀ ω, (∫ t in (0 : ℝ)..σ ω, (σ ω - t) * a (ω, t)) =
      ∫ t in (0 : ℝ)..1, (σ ω - t) * a (ω, t) := by
    intro ω
    apply integral_until_eq_full (hσ0 ω) (hσ1 ω) (hWI ω)
    intro t ht
    rw [hsupport ω t ht.1 ht.2, mul_zero]
  have hA : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..σ ω, a (ω, t)) μ := by
    simpa only [hAe, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using ha.integral_prod_left
  have hB : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..σ ω, (σ ω - t) * a (ω, t)) μ := by
    simpa only [hBe, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using hW.integral_prod_left
  have haShort : ∀ ω, IntervalIntegrable (fun t ↦ a (ω, t)) volume 0 (σ ω) := by
    intro ω
    exact (haI ω).mono_set (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), uIcc_of_le (hσ0 ω)] using Icc_subset_Icc le_rfl (hσ1 ω))
  have hquad := averaged_selection_duration μ hσ0 hσ1 haShort
    (fun ω t ht ↦ ha0 ω t ⟨ht.1, ht.2.trans (hσ1 ω)⟩)
    (fun ω t ht ↦ ha1 ω t ⟨ht.1, ht.2.trans (hσ1 ω)⟩) hA hB
  have hinner : ∀ ω, (∫ t in (0 : ℝ)..σ ω, (σ ω - t) * a (ω, t)) ≤
      σ ω - ∫ t in (0 : ℝ)..1, τ (ω, t) := by
    intro ω
    rw [hBe ω]
    have h := intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1)
      (hWI ω) (intervalIntegrable_const.sub (hτI ω)) (hgap ω)
    simpa only [intervalIntegral.integral_sub intervalIntegrable_const (hτI ω),
      intervalIntegral.integral_const, sub_zero, one_smul] using h
  have hT : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..1, τ (ω, t)) μ := by
    simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using hτ.integral_prod_left
  have hbound := integral_mono hB (hσ.sub hT) hinner
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub (f := σ) (g := fun ω ↦ ∫ t in (0 : ℝ)..1, τ (ω, t)) hσ hT] at hbound
  have hfinish := hquad.trans hbound
  simp only [hAe, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at hfinish
  simpa only [integral_prod _ ha, integral_prod _ hτ] using hfinish

end ProphetSecretary.Reach
