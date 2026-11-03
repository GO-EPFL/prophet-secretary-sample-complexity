import ProphetSecretary.Statistics.DurationCalibration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# Independent-sample duration calibration

The least root of the empirical mean curve is measurable. Omitting one
observation gives the finite leave-one-out inequality, and the product-law
coordinate decomposition identifies the mean held-out error with the
population error of a fresh calibration sample. Paper: `lem:duration-calibration`.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics
namespace Calibration

variable {Y : Type*} {m : ℕ}

/-- The empirical duration curve from a complete validation sample. -/
noncomputable def empiricalCurve (f : ℝ → Y → ℝ) (y : Fin m → Y) (t : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, f t (y i)

lemma empiricalCurve_continuous (f : ℝ → Y → ℝ)
    (hc : ∀ y, Continuous (fun t => f t y)) (y : Fin m → Y) :
    Continuous (empiricalCurve f y) := by
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ => hc (y i)))

lemma empiricalCurve_monotone (f : ℝ → Y → ℝ)
    (hmono : ∀ y, Monotone (fun t => f t y)) (y : Fin m → Y) :
    Monotone (empiricalCurve f y) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hmono (y i) hst)) (by positivity)

lemma empiricalCurve_zero (f : ℝ → Y → ℝ) (h0 : ∀ y, f 0 y = 0) (y : Fin m → Y) :
    empiricalCurve f y 0 = 0 := by simp [empiricalCurve, h0]

lemma empiricalCurve_one [NeZero m] (f : ℝ → Y → ℝ) (h1 : ∀ y, f 1 y = 1) (y : Fin m → Y) :
    empiricalCurve f y 1 = 1 := by
  simp only [empiricalCurve, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast NeZero.ne m)

lemma empiricalCurve_measurable [MeasurableSpace Y] (f : ℝ → Y → ℝ)
    (hf : Measurable (Function.uncurry f)) (t : ℝ) :
    Measurable (fun y : Fin m → Y => empiricalCurve f y t) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact hf.comp (measurable_const.prodMk (measurable_pi_apply i))

/-- The least validation root, including deterministic resolution of flat pieces. -/
noncomputable def parameter (f : ℝ → Y → ℝ) (ρ : ℝ) (y : Fin m → Y) : ℝ :=
  durationCalibrationRoot (empiricalCurve f y) ρ

lemma parameter_isLeast [NeZero m] (f : ℝ → Y → ℝ)
    (hc : ∀ y, Continuous (fun t => f t y))
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (y : Fin m → Y) :
    IsLeast {t | t ∈ Icc (0 : ℝ) 1 ∧ empiricalCurve f y t = ρ} (parameter f ρ y) :=
  durationCalibrationRoot_isLeast _ (empiricalCurve_continuous f hc y)
    (empiricalCurve_zero f h0 y) (empiricalCurve_one f h1 y) hρ

lemma measurable_parameter [MeasurableSpace Y] [NeZero m] (f : ℝ → Y → ℝ)
    (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) : Measurable (parameter (m := m) f ρ) :=
  measurable_durationCalibrationRoot (empiricalCurve f) (fun _ => ρ)
    (empiricalCurve_continuous f hc) (empiricalCurve_monotone f hmono)
    (empiricalCurve_zero f h0) (empiricalCurve_one f h1)
    (empiricalCurve_measurable f hf) measurable_const (fun _ => hρ)

/-- The least root after removing the indicated observation. -/
noncomputable def omittedParameter (f : ℝ → Y → ℝ) (ρ : ℝ)
    (y : Fin (m+1) → Y) (i : Fin (m+1)) : ℝ :=
  parameter f ρ (fun j : Fin m => y (i.succAbove j))

lemma omitted_root_sum [NeZero m] (f : ℝ → Y → ℝ)
    (hc : ∀ y, Continuous (fun t => f t y))
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (y : Fin (m+1) → Y) (i : Fin (m+1)) :
    ∑ j ∈ Finset.univ.erase i, (f (omittedParameter f ρ y i) (y j) - ρ) = 0 := by
  have hr := (parameter_isLeast f hc h0 h1 hρ (fun j : Fin m => y (i.succAbove j))).1.2
  have hcount : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hs : ∑ j : Fin m, f (omittedParameter f ρ y i) (y (i.succAbove j)) = (m : ℝ)*ρ := by
    change (m : ℝ)⁻¹ * (∑ j : Fin m, f (omittedParameter f ρ y i) (y (i.succAbove j))) = ρ at hr
    apply (mul_left_cancel₀ (inv_ne_zero hcount))
    simpa [hcount] using hr
  have he : (∑ j ∈ Finset.univ.erase i, (f (omittedParameter f ρ y i) (y j) - ρ)) =
      ∑ j : Fin m, (f (omittedParameter f ρ y i) (y (i.succAbove j)) - ρ) := by
    have hA := Fin.sum_univ_succAbove (fun j => f (omittedParameter f ρ y i) (y j) - ρ) i
    have hB := Finset.sum_erase_add (Finset.univ : Finset (Fin (m+1)))
      (fun j => f (omittedParameter f ρ y i) (y j) - ρ) (Finset.mem_univ i)
    linarith
  rw [he, Finset.sum_sub_distrib, hs]
  simp

/-- The held-out errors obey the paper's pathwise sum bound. -/
lemma omitted_sum_abs_le_one [NeZero m] (f : ℝ → Y → ℝ)
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (y : Fin (m+1) → Y) :
    |∑ i, (f (omittedParameter f ρ y i) (y i) - ρ)| ≤ 1 := by
  exact calibration_leaveOneOut_sum_bounds (fun t i => f t (y i))
    (omittedParameter f ρ y) hρ (fun i => hmono (y i))
    (fun i => hrange _ _) (fun i => omitted_root_sum f hc h0 h1 hρ y i)

/-- The population mean duration curve. -/
noncomputable def populationCurve [MeasurableSpace Y] (μ : Measure Y) (f : ℝ → Y → ℝ) (t : ℝ) : ℝ :=
  ∫ y, f t y ∂μ

lemma populationCurve_measurable [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f)) :
    Measurable (populationCurve μ f) :=
  hf.stronglyMeasurable.integral_prod_right.measurable

lemma integrable_section [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Integrable (f t) μ := by
  apply Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun y => by
    change ‖f t y‖ ≤ 1
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hrange t y).1] using (hrange t y).2

lemma populationCurve_range [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    populationCurve μ f t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun y => (hrange t y).1), ?_⟩
  have h := integral_mono (integrable_section μ f hf hrange t) (integrable_const (1 : ℝ))
    (fun y => (hrange t y).2)
  simpa only [populationCurve, integral_const, probReal_univ, one_smul] using h

/-- Population calibration error of the root selected from `m` observations. -/
noncomputable def error [MeasurableSpace Y] (μ : Measure Y) (f : ℝ → Y → ℝ) (ρ : ℝ) (y : Fin m → Y) : ℝ :=
  populationCurve μ f (parameter f ρ y) - ρ

lemma measurable_error [MeasurableSpace Y] [NeZero m] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) : Measurable (error (m := m) μ f ρ) :=
  ((populationCurve_measurable μ f hf).comp
    (measurable_parameter f hf hc hmono h0 h1 hρ)).sub_const ρ

lemma error_abs_le_one [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (y : Fin m → Y) :
    |error μ f ρ y| ≤ 1 := by
  have hp := populationCurve_range μ f hf hrange (parameter f ρ y)
  exact abs_le.mpr ⟨by dsimp [error]; linarith [hp.1, hρ.2],
    by dsimp [error]; linarith [hp.2, hρ.1]⟩

/-- Removing a coordinate really leaves an independent fresh observation. -/
lemma integral_omitted_error [MeasurableSpace Y] [NeZero m] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (i : Fin (m+1)) :
    (∫ y : Fin (m+1) → Y, f (omittedParameter f ρ y i) (y i) - ρ
      ∂Measure.pi (fun _ => μ)) =
      ∫ y : Fin m → Y, error μ f ρ y ∂Measure.pi (fun _ => μ) := by
  let H : Y × (Fin m → Y) → ℝ := fun q => f (parameter f ρ q.2) q.1 - ρ
  have hH : Measurable H :=
    (hf.comp (((measurable_parameter f hf hc hmono h0 h1 hρ).comp measurable_snd).prodMk
      measurable_fst)).sub_const ρ
  have hHI : Integrable H (μ.prod (Measure.pi (fun _ : Fin m => μ))) := by
    apply Integrable.of_bound hH.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun q => by
      change ‖f (parameter f ρ q.2) q.1 - ρ‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(hrange (parameter f ρ q.2) q.1).1, hρ.2],
        by linarith [(hrange (parameter f ρ q.2) q.1).2, hρ.1]⟩
  have hSplit := (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) i).integral_comp' H
  change (∫ y : Fin (m+1) → Y,
    H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Y) i) y)
      ∂Measure.pi (fun _ => μ)) = _
  rw [hSplit, integral_prod _ hHI]
  rw [integral_integral_swap hHI]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (∫ a, f (parameter f ρ y) a - ρ ∂μ) = populationCurve μ f (parameter f ρ y) - ρ
    rw [integral_sub (integrable_section μ f hf hrange _) (integrable_const ρ),
      integral_const, probReal_univ, one_smul]
    rfl

/-- The expected signed error has the exact inverse-sample bias rate. -/
theorem integral_error_abs_le [MeasurableSpace Y] [NeZero m] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    |∫ y : Fin m → Y, error μ f ρ y ∂Measure.pi (fun _ => μ)| ≤ 1 / ((m : ℝ)+1) := by
  let Ξ := Fin (m+1) → Y
  let ν : Measure Ξ := Measure.pi (fun _ => μ)
  let E : Fin (m+1) → Ξ → ℝ := fun i y => f (omittedParameter f ρ y i) (y i) - ρ
  have hE (i : Fin (m+1)) : Integrable (E i) ν := by
    have hparam : Measurable (fun y : Ξ => omittedParameter f ρ y i) :=
      (measurable_parameter f hf hc hmono h0 h1 hρ).comp (by fun_prop)
    apply Integrable.of_bound ((hf.comp (hparam.prodMk (measurable_pi_apply i))).sub_const ρ).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun y => by
      change ‖f (omittedParameter f ρ y i) (y i) - ρ‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(hrange (omittedParameter f ρ y i) (y i)).1, hρ.2],
        by linarith [(hrange (omittedParameter f ρ y i) (y i)).2, hρ.1]⟩
  have hsumI := integrable_finsetSum Finset.univ (fun i _ => hE i)
  have hsum (y : Ξ) : |∑ i, E i y| ≤ 1 := omitted_sum_abs_le_one f hc hmono hrange h0 h1 hρ y
  have hBound : |∫ y, ∑ i, E i y ∂ν| ≤ 1 := by
    apply (abs_integral_le_integral_abs).trans
    have h := integral_mono hsumI.abs (integrable_const (1 : ℝ)) hsum
    simpa only [integral_const, probReal_univ, one_smul] using h
  have he : (∫ y, ∑ i, E i y ∂ν) =
      ((m : ℝ)+1) * (∫ y : Fin m → Y, error μ f ρ y ∂Measure.pi (fun _ => μ)) := by
    rw [integral_finsetSum _ (fun i _ => hE i)]
    simp_rw [show ∀ i, (∫ y, E i y ∂ν) =
      ∫ y : Fin m → Y, error μ f ρ y ∂Measure.pi (fun _ => μ) from
      fun i => integral_omitted_error μ f hf hc hmono hrange h0 h1 hρ i]
    simp
  rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ)+1)] at hBound
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ)+1)).mpr (by simpa [mul_comm] using hBound)

end Calibration
end ProphetSecretary.Statistics
