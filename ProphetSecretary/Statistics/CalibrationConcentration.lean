import ProphetSecretary.Statistics.CalibrationMoments
import ProphetSecretary.Probability.BoundedCDFMean
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Concentration of the calibrated population duration

A positive population error forces a deviation at a deterministic population
quantile. Hoeffding's inequality at that one quantile gives a Gaussian tail,
whose integral proves the calibration second-moment bound. This argument
uses no uniform empirical-process theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Statistics.Calibration

variable {Y : Type*} [MeasurableSpace Y] {m : ℕ} [NeZero m]

lemma populationCurve_continuous (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1) : Continuous (populationCurve μ f) := by
  apply continuous_of_dominated
    (fun t => (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall fun y => ?_)
    (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall hc)
  change ‖f t y‖ ≤ 1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hrange t y).1] using (hrange t y).2

lemma populationCurve_monotone (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1) : Monotone (populationCurve μ f) := by
  intro s t hst
  exact integral_mono (integrable_section μ f hf hrange s) (integrable_section μ f hf hrange t)
    (fun y => hmono y hst)

lemma populationCurve_zero (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (h0 : ∀ y, f 0 y = 0) : populationCurve μ f 0 = 0 := by
  simp [populationCurve, h0]

lemma populationCurve_one (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (h1 : ∀ y, f 1 y = 1) : populationCurve μ f 1 = 1 := by
  simp [populationCurve, h1]

lemma empiricalCurve_upper_tail (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1) (t : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {y | populationCurve μ f t + δ ≤ empiricalCurve f y t} ≤
      Real.exp (-(m : ℝ)*δ^2/2) := by
  let ν : Measure (Fin m → Y) := Measure.pi (fun _ => μ)
  let M := populationCurve μ f t
  let X : Fin m → (Fin m → Y) → ℝ := fun i y => f t (y i) - M
  have hfT : Measurable (f t) := hf.comp (measurable_const.prodMk measurable_id)
  have hM := populationCurve_range μ f hf hrange t
  have hXi (i : Fin m) : Integrable (fun y : Fin m → Y => f t (y i)) ν :=
    (measurePreserving_eval (fun _ : Fin m => μ) i).integrable_comp_of_integrable
      (integrable_section μ f hf hrange t)
  have hmean (i : Fin m) : (∫ y : Fin m → Y, f t (y i) ∂ν) = M := by
    exact (measurePreserving_eval (fun _ : Fin m => μ) i).hasLaw.integral_comp hfT.aestronglyMeasurable
  have hsub (i : Fin m) : HasSubgaussianMGF (X i) 1 ν := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((hfT.comp (measurable_pi_apply i)).sub_const M).aemeasurable
      (Filter.Eventually.of_forall fun y : Fin m → Y =>
        show (f t (y i) - M) ∈ Icc (-1 : ℝ) 1 from
          ⟨by dsimp [M]; linarith [(hrange t (y i)).1, hM.2],
           by dsimp [M]; linarith [(hrange t (y i)).2, hM.1]⟩)
      (show (∫ y : Fin m → Y, f t (y i) - M ∂ν) = 0 by
        rw [integral_sub (hXi i) (integrable_const M), hmean, integral_const, probReal_univ, one_smul, sub_self])
    norm_num at h
    exact h
  have hind : iIndepFun X ν :=
    iIndepFun_pi (fun _ : Fin m => (hfT.sub_const M).aemeasurable)
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => (1 : ℝ≥0)) (fun i _ => hsub i)
    (mul_nonneg (Nat.cast_nonneg m) hδ)
  have hinc : {y | M + δ ≤ empiricalCurve f y t} ⊆
      {y | (m : ℝ)*δ ≤ ∑ i : Fin m, X i y} := by
    intro y hy
    have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    have h := mul_le_mul_of_nonneg_left hy hmpos.le
    change (m : ℝ)*(M+δ) ≤ (m : ℝ)*((m : ℝ)⁻¹ * ∑ i, f t (y i)) at h
    rw [← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul] at h
    change (m : ℝ)*δ ≤ ∑ i, (f t (y i)-M)
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  apply (measureReal_mono hinc).trans (htail.trans_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, NNReal.coe_natCast]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp [hm]

lemma empiricalCurve_lower_tail (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1) (t : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {y | empiricalCurve f y t ≤ populationCurve μ f t - δ} ≤
      Real.exp (-(m : ℝ)*δ^2/2) := by
  let g : ℝ → Y → ℝ := fun t y => 1-f t y
  have hg : Measurable (Function.uncurry g) := measurable_const.sub hf
  have hgr : ∀ t y, g t y ∈ Icc (0 : ℝ) 1 := fun t y =>
    ⟨by dsimp [g]; linarith [(hrange t y).2], by dsimp [g]; linarith [(hrange t y).1]⟩
  have hPop : populationCurve μ g t = 1-populationCurve μ f t := by
    rw [populationCurve, integral_sub (integrable_const _) (integrable_section μ f hf hrange t)]
    simp only [integral_const, probReal_univ, one_smul, populationCurve]
  have hEmp (y : Fin m → Y) : empiricalCurve g y t = 1-empiricalCurve f y t := by
    dsimp [empiricalCurve, g]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    field_simp
  have he : {y : Fin m → Y | empiricalCurve f y t ≤ populationCurve μ f t - δ} =
      {y | populationCurve μ g t + δ ≤ empiricalCurve g y t} := by
    ext y
    simp only [Set.mem_setOf_eq, hPop, hEmp]
    constructor <;> intro h <;> linarith
  rw [he]
  exact empiricalCurve_upper_tail μ g hg hgr t hδ

/-- Positive population error implies a deviation at one deterministic quantile. -/
lemma error_upper_tail (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ δ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real {y | δ < error μ f ρ y} ≤
      Real.exp (-(m : ℝ)*δ^2/2) := by
  by_cases hEnd : ρ+δ ≤ 1
  · let t := durationCalibrationRoot (populationCurve μ f) (ρ+δ)
    have ht := durationCalibrationRoot_isLeast (populationCurve μ f)
      (populationCurve_continuous μ f hf hc hrange) (populationCurve_zero μ f h0)
      (populationCurve_one μ f h1) (show ρ+δ ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hρ.1], hEnd⟩)
    have hinc : {y : Fin m → Y | δ < error μ f ρ y} ⊆
        {y | empiricalCurve f y t ≤ populationCurve μ f t - δ} := by
      intro y hy
      have hr := parameter_isLeast f hc h0 h1 hρ y
      have hlt : t < parameter f ρ y := by
        by_contra hn
        have hle := populationCurve_monotone μ f hf hmono hrange (le_of_not_gt hn)
        dsimp [error] at hy
        change populationCurve μ f (parameter f ρ y) ≤ populationCurve μ f t at hle
        have hte : populationCurve μ f t = ρ+δ := ht.1.2
        linarith
      have he := empiricalCurve_monotone f hmono y hlt.le
      have hte : populationCurve μ f t = ρ+δ := ht.1.2
      rw [hr.1.2]
        at he
      change empiricalCurve f y t ≤ populationCurve μ f t - δ
      linarith
    exact (measureReal_mono hinc).trans (empiricalCurve_lower_tail μ f hf hrange t hδ)
  · have he : {y : Fin m → Y | δ < error μ f ρ y} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hy
      have h := (populationCurve_range μ f hf hrange (parameter f ρ y)).2
      dsimp [error] at hy
      linarith
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le

lemma error_lower_tail (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ δ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real {y | error μ f ρ y < -δ} ≤
      Real.exp (-(m : ℝ)*δ^2/2) := by
  by_cases hEnd : 0 ≤ ρ-δ
  · let t := durationCalibrationRoot (populationCurve μ f) (ρ-δ)
    have ht := durationCalibrationRoot_isLeast (populationCurve μ f)
      (populationCurve_continuous μ f hf hc hrange) (populationCurve_zero μ f h0)
      (populationCurve_one μ f h1) (show ρ-δ ∈ Icc (0 : ℝ) 1 from ⟨hEnd, by linarith [hρ.2]⟩)
    have hinc : {y : Fin m → Y | error μ f ρ y < -δ} ⊆
        {y | populationCurve μ f t + δ ≤ empiricalCurve f y t} := by
      intro y hy
      have hr := parameter_isLeast f hc h0 h1 hρ y
      have hlt : parameter f ρ y < t := by
        by_contra hn
        have hle := populationCurve_monotone μ f hf hmono hrange (le_of_not_gt hn)
        dsimp [error] at hy
        change populationCurve μ f t ≤ populationCurve μ f (parameter f ρ y) at hle
        have hte : populationCurve μ f t = ρ-δ := ht.1.2
        linarith
      have he := empiricalCurve_monotone f hmono y hlt.le
      have hte : populationCurve μ f t = ρ-δ := ht.1.2
      rw [hr.1.2] at he
      change populationCurve μ f t + δ ≤ empiricalCurve f y t
      linarith
    exact (measureReal_mono hinc).trans (empiricalCurve_upper_tail μ f hf hrange t hδ)
  · have he : {y : Fin m → Y | error μ f ρ y < -δ} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hy
      have h := (populationCurve_range μ f hf hrange (parameter f ρ y)).1
      dsimp [error] at hy
      linarith
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le

/-- A Gaussian calibration tail with a universal constant. -/
theorem error_abs_tail (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ δ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real {y | δ < |error μ f ρ y|} ≤
      2*Real.exp (-(m : ℝ)*δ^2/2) := by
  have he : {y : Fin m → Y | δ < |error μ f ρ y|} =
      {y | δ < error μ f ρ y} ∪ {y | error μ f ρ y < -δ} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_union, lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [he]
  have hU := measureReal_union_le
    (μ := Measure.pi (fun _ : Fin m => μ)) {y | δ < error μ f ρ y}
    {y | error μ f ρ y < -δ}
  have hP := error_upper_tail (m := m) μ f hf hc hmono hrange h0 h1 hρ hδ
  have hN := error_lower_tail (m := m) μ f hf hc hmono hrange h0 h1 hρ hδ
  linarith

private lemma integral_two_exp_le {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioc (0 : ℝ) 1, 2*Real.exp (-a*t)) ≤ 2/a := by
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr ha.ne'),
    integral_exp]
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  have he : 2*((-a)⁻¹*(Real.exp (-a)-1)) = (2/a)*(1-Real.exp (-a)) := by
    field_simp
    ring
  rw [he]
  exact mul_le_of_le_one_right (by positivity) (by linarith [Real.exp_pos (-a)])

/-- The second-moment clause of `lem:duration-calibration`, with explicit constant. -/
theorem integral_error_sq_le (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : ℝ → Y → ℝ) (hf : Measurable (Function.uncurry f))
    (hc : ∀ y, Continuous (fun t => f t y))
    (hmono : ∀ y, Monotone (fun t => f t y))
    (hrange : ∀ t y, f t y ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ y, f 0 y = 0) (h1 : ∀ y, f 1 y = 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    (∫ y : Fin m → Y, error μ f ρ y ^ 2 ∂Measure.pi (fun _ => μ)) ≤ 4/(m : ℝ) := by
  let ν : Measure (Fin m → Y) := Measure.pi (fun _ => μ)
  let G : (Fin m → Y) → ℝ := fun y => error μ f ρ y ^ 2
  have hGm : Measurable G := (measurable_error μ f hf hc hmono h0 h1 hρ).pow_const 2
  have hGr : ∀ᵐ y ∂ν, G y ∈ Icc (0 : ℝ) (1 : ℝ≥0) :=
    Filter.Eventually.of_forall fun y => by
      have h := error_abs_le_one μ f hf hrange hρ y
      refine ⟨sq_nonneg _, ?_⟩
      have hs := pow_le_pow_left₀ (abs_nonneg (error μ f ρ y)) h 2
      change error μ f ρ y ^ 2 ≤ (1 : ℝ)
      simpa only [sq_abs, one_pow] using hs
  change (∫ y, G y ∂ν) ≤ _
  rw [ProphetSecretary.Probability.integral_eq_bounded_strict_layercake ν hGm (1 : ℝ≥0) hGr]
  change (∫ t in Ioc (0 : ℝ) (1 : ℝ), ν.real {y | t < G y}) ≤ 4/(m : ℝ)
  have hTailI : IntegrableOn (fun t : ℝ => ν.real {y | t < G y}) (Ioc (0 : ℝ) 1) := by
    have hm : Antitone (fun t : ℝ => ν.real {y | t < G y}) :=
      fun _ _ hst => measureReal_mono (fun _ ht => hst.trans_lt ht)
    apply Integrable.of_bound hm.measurable.aestronglyMeasurable.restrict 1
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hExpC : Continuous (fun t : ℝ => 2*Real.exp (-(m : ℝ)/2*t)) := by fun_prop
  have hExpI : IntegrableOn (fun t : ℝ => 2*Real.exp (-(m : ℝ)/2*t)) (Icc (0 : ℝ) 1) volume :=
    hExpC.integrableOn_Icc
  have hBound : (∫ t in Ioc (0 : ℝ) 1, ν.real {y | t < G y}) ≤
      ∫ t in Ioc (0 : ℝ) 1, 2*Real.exp (-(m : ℝ)/2*t) := by
    apply integral_mono_ae hTailI (hExpI.mono_set Ioc_subset_Icc_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hinc : {y | t < G y} ⊆ {y | Real.sqrt t < |error μ f ρ y|} := by
      intro y hy
      change t < error μ f ρ y ^ 2 at hy
      change Real.sqrt t < |error μ f ρ y|
      by_contra hn
      have hle := le_of_not_gt hn
      have hsq := pow_le_pow_left₀ (abs_nonneg (error μ f ρ y)) hle 2
      rw [sq_abs, Real.sq_sqrt ht.1.le] at hsq
      exact not_lt_of_ge hsq hy
    have h := (measureReal_mono hinc).trans
      (error_abs_tail μ f hf hc hmono hrange h0 h1 hρ (Real.sqrt_nonneg t))
    apply h.trans_eq
    rw [Real.sq_sqrt ht.1.le]
    congr 2
    ring
  apply hBound.trans
  have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have h := integral_two_exp_le (div_pos hmpos (by norm_num : (0 : ℝ) < 2))
  have he : 2/((m : ℝ)/2) = 4/(m : ℝ) := by
    field_simp
    norm_num
  simpa only [neg_div] using h.trans_eq he

end ProphetSecretary.Statistics.Calibration
