import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The lower fraction of an ordered nonnegative random variable

If a measurable lower event separates numerical values at a fixed cutoff, its
share of the first moment is at most its probability share. No absence of atoms
or strict inequality at the cutoff is required.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Probability
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem lower_split_integral_le_probability_mul {X : Ω → ℝ} (hX : Integrable X μ)
    {A : Set Ω} (hA : MeasurableSet A) {c : ℝ}
    (hLow : ∀ᵐ ω ∂μ, ω∈A → X ω≤c) (hHigh : ∀ᵐ ω ∂μ, ω∉A → c≤X ω) :
    (∫ ω in A, X ω ∂μ)≤μ.real A*(∫ ω, X ω ∂μ) := by
  let q := μ.real A
  let a := ∫ ω in A, X ω ∂μ
  let b := ∫ ω in Aᶜ, X ω ∂μ
  have hq0 : 0≤q := measureReal_nonneg
  have hq1 : q≤1 := measureReal_le_one
  have hAInt := hX.indicator hA
  have hBInt := hX.indicator hA.compl
  have hLoInt := integral_mono_ae hAInt ((integrable_const c).indicator hA) (by
    filter_upwards [hLow] with ω hω
    by_cases h : ω∈A
    · simpa only [Set.indicator_of_mem h] using hω h
    · simp only [Set.indicator_of_notMem h,le_refl])
  have hHiInt := integral_mono_ae ((integrable_const c).indicator hA.compl) hBInt (by
    filter_upwards [hHigh] with ω hω
    by_cases h : ω∈A
    · simp only [Set.indicator_of_notMem (show ω∉Aᶜ from fun hc => hc h),le_refl]
    · simpa only [Set.indicator_of_mem (show ω∈Aᶜ from h)] using hω h)
  have ha : a≤q*c := by simpa only [a,q,integral_indicator hA,integral_indicator_const _ hA,setIntegral_const,smul_eq_mul] using hLoInt
  have hb : (1-q)*c≤b := by
    simpa only [b,q,integral_indicator hA.compl,integral_indicator_const _ hA.compl,setIntegral_const,probReal_compl_eq_one_sub hA,smul_eq_mul] using hHiInt
  have hMean : a+b=∫ ω, X ω ∂μ := by
    exact integral_add_compl hA hX
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hq1)
  have h2 := mul_le_mul_of_nonneg_left hb hq0
  change a≤q*(∫ ω, X ω ∂μ)
  rw [←hMean]
  nlinarith only [h1,h2]

/-- The complementary upper fraction carries at least its probability share. -/
theorem upper_split_integral_ge_probability_mul {X : Ω → ℝ} (hX : Integrable X μ)
    {A : Set Ω} (hA : MeasurableSet A) {c : ℝ}
    (hLow : ∀ᵐ ω ∂μ, ω∈A → X ω≤c) (hHigh : ∀ᵐ ω ∂μ, ω∉A → c≤X ω) :
    (1-μ.real A)*(∫ ω, X ω ∂μ)≤∫ ω in Aᶜ, X ω ∂μ := by
  have h := lower_split_integral_le_probability_mul μ hX hA hLow hHigh
  have hMean := integral_add_compl hA hX
  linarith only [h,hMean]

end ProphetSecretary.Probability
