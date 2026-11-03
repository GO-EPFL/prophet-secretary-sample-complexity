import ProphetSecretary.Statistics.FirstProjectionGap
import ProphetSecretary.Model.ScalarRatio
import ProphetSecretary.Probability.ScorePayoffComparison

/-!
# Sampling variance of the calibration target's frozen optimal kernel

The first-order Hoeffding component is controlled by law curvature at the
fixed true-law optimizer. Higher-order components contribute at most `1/m²`.
At a ratio-minimizing weight the scalar gap is the ratio slack times its
benchmark denominator. These are the variance steps in `lem:calibration-target`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

/-- Orthogonality separates the actual empirical first-order and higher-order variances. -/
lemma variance_empiricalMean_eq_first_add_higher (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (empiricalMean (k := k) f) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      variance (firstOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) +
      variance (higherOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
  let A := firstOrderEmpirical (k := k) μ f
  let B := higherOrderEmpirical (k := k) μ f
  let c := ∫ x, f x ∂Measure.pi μ
  have hA := memLp_firstOrderEmpirical_of_ae_bounded (k := k) μ hf C hb 2
  have hB := memLp_higherOrderEmpirical_of_ae_bounded (k := k) μ hf C hb 2
  have he : empiricalMean (k := k) f = fun y => (A y+B y)+c := by
    funext y
    have h := empiricalMean_order_decomposition (k := k) μ f y
    dsimp only [A, B, c]
    linarith
  rw [he]
  calc
    _ = variance (firstOrderEmpirical (k := k) μ f + higherOrderEmpirical (k := k) μ f)
        (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
      simpa only [A, B, Pi.add_apply] using variance_add_const (hA.add hB).aestronglyMeasurable c
    _ = _ := by
      have hv := variance_add hA hB
      have hcov := covariance_first_higher_of_ae_bounded (k := k) μ hf C hb
      simpa only [hcov, mul_zero, add_zero] using hv

/-- A refined product-empirical variance bound, with an explicit higher-order term. -/
theorem variance_empiricalMean_le_firstProjection (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (empiricalMean (k := k) f) (Measure.pi (fun q : ι × Fin k => μ q.1)) ≤
      (k : ℝ)⁻¹ * (∑ i : ι, ∫ a, firstProjection μ f i a ^ 2 ∂μ i) +
        (C : ℝ)^2/(k : ℝ)^2 := by
  rw [variance_empiricalMean_eq_first_add_higher μ hf C hb,
    variance_firstOrderEmpirical_of_ae_bounded μ hf C hb]
  exact add_le_add le_rfl (variance_higherOrderEmpirical_of_ae_bounded (k := k) μ hf C hb)


omit [DecidableEq ι] in
/-- Almost-everywhere bounded kernels retain all empirical finite moments. -/
lemma memLp_empiricalMean_of_ae_bounded (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (p : ENNReal) :
    MemLp (empiricalMean (k := k) f) p (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
  let g := boundedRepresentative C f
  have hg := measurable_boundedRepresentative C hf
  have he : g =ᵐ[Measure.pi μ] f := boundedRepresentative_ae_eq C hb
  exact (memLp_congr_ae (empiricalMean_congr_ae (k := k) μ he)).mp
    (memLp_empiricalMean μ hg C (boundedRepresentative_abs_le C f) p)

omit [DecidableEq ι] in
/-- Independent product-empirical averaging preserves any almost-everywhere bounded kernel mean. -/
lemma integral_empiricalMean_of_ae_bounded (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    (∫ y, empiricalMean (k := k) f y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) =
      ∫ x, f x ∂Measure.pi μ := by
  let g := boundedRepresentative C f
  have hgm := measurable_boundedRepresentative C hf
  have he : g =ᵐ[Measure.pi μ] f := boundedRepresentative_ae_eq C hb
  calc
    _ = ∫ y, empiricalMean (k := k) g y ∂Measure.pi (fun q : ι × Fin k => μ q.1) :=
      (integral_congr_ae (empiricalMean_congr_ae (k := k) μ he)).symm
    _ = ∫ x, g x ∂Measure.pi μ := integral_empiricalMean μ hgm C (boundedRepresentative_abs_le C f)
    _ = _ := integral_congr_ae he

end ProphetSecretary.Statistics.Hoeffding

namespace ProphetSecretary.Model
open ProphetSecretary.Statistics.Hoeffding

variable {n k : ℕ} [NeZero k]


/-- The empirical frozen-optimum kernel is unbiased for the true scalar gap. -/
lemma RandomizedPolicy.integral_empiricalGameKernel (π : RandomizedPolicy n)
    (P : Instance n) (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1)
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    (∫ y, empiricalMean (k := k) (π.normalizedGameKernel lam) y ∂P.trainingCoordinateLaw k) =
      normalizedScalarGap P lam := by
  change (∫ y, empiricalMean (k := k) (π.normalizedGameKernel lam) y
    ∂Measure.pi (fun q : Fin n × Fin k => P.law q.1)) = _
  rw [integral_empiricalMean_of_ae_bounded P.law (π.measurable_normalizedGameKernel lam) 1
    (π.normalizedGameKernel_abs_le_ae P hcap hlam)]
  have h := π.integral_normalizedGameKernel P hcap hlam
  rw [hOpt] at h
  exact h

/-- The frozen true-law optimal kernel has variance controlled by its scalar gap. -/
theorem RandomizedPolicy.empiricalGameKernel_variance_le_gap (π : RandomizedPolicy n)
    (P : Instance n) (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1-δ))
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    variance (empiricalMean (k := k) (π.normalizedGameKernel lam)) (P.trainingCoordinateLaw k) ≤
      pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*normalizedScalarGap P lam/(k : ℝ) +
        1/(k : ℝ)^2 := by
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1, by linarith [hlam.2]⟩
  have hf := π.measurable_normalizedGameKernel lam
  have hb := π.normalizedGameKernel_abs_le_ae P hcap hLam
  have h := variance_empiricalMean_le_firstProjection (k := k) P.law hf 1 hb
  have hFirst := π.firstProjection_variance_le_normalizedGap P hcap hδ hlam hOpt
  have hScale := mul_le_mul_of_nonneg_left hFirst (inv_nonneg.mpr (Nat.cast_nonneg k))
  unfold Instance.firstProjectionVariance at hScale
  change variance _ (Measure.pi (fun q : Fin n × Fin k => P.law q.1)) ≤ _
  norm_num only [NNReal.coe_one, one_pow] at h
  have hx := add_le_add hScale (le_refl (1/(k : ℝ)^2))
  exact h.trans (hx.trans_eq (by ring))

/-- At a ratio-minimizing interior weight the variance is controlled by ratio slack. -/
theorem RandomizedPolicy.empiricalGameKernel_variance_le_ratioSlack (π : RandomizedPolicy n)
    (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) (hM : P.expectedMaximum ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1-δ))
    (hmin : P.optimalScalarRatio = P.normalizedScalarRatio lam)
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    variance (empiricalMean (k := k) (π.normalizedGameKernel lam)) (P.trainingCoordinateLaw k) ≤
      pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*
        (P.optimalScalarRatio-optimalCompetitiveRatio)/(k : ℝ) + 1/(k : ℝ)^2 := by
  have h01 : lam ∈ Icc (0 : ℝ) 1 := ⟨hδ.le.trans hlam.1, by linarith [hlam.2]⟩
  have hs : 0 ≤ P.optimalScalarRatio-optimalCompetitiveRatio :=
    sub_nonneg.mpr (P.optimalScalarRatio_bounds hP).1
  have hden : lam*P.expectedMaximum+1-lam ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hM h01.1
    linarith
  have hgap : normalizedScalarGap P lam ≤ P.optimalScalarRatio-optimalCompetitiveRatio := by
    rw [P.normalizedScalarGap_at_ratio_minimizer hP h01 hmin]
    have h := mul_le_mul_of_nonneg_left hden hs
    simpa only [mul_one] using h
  have hCoeff : 0 ≤ pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)/(k : ℝ) := by
    have hC := (pilotFirstProjectionConstant_positive hδ).le
    have hS := P.totalFirstMoment_nonnegative
    positivity
  have h := π.empiricalGameKernel_variance_le_gap (k := k) P hcap hδ hlam hOpt
  have hmul := mul_le_mul_of_nonneg_left hgap hCoeff
  apply h.trans
  calc
    _ = (pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)/(k : ℝ))*normalizedScalarGap P lam +
        1/(k : ℝ)^2 := by ring
    _ ≤ (pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)/(k : ℝ))*
        (P.optimalScalarRatio-optimalCompetitiveRatio) + 1/(k : ℝ)^2 := add_le_add hmul le_rfl
    _ = _ := by ring

/-- The centered frozen-optimum kernel has the near-critical first-moment rate. -/
theorem RandomizedPolicy.empiricalGameKernel_L1_error_le_ratioSlack (π : RandomizedPolicy n)
    (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) (hM : P.expectedMaximum ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1-δ))
    (hmin : P.optimalScalarRatio = P.normalizedScalarRatio lam)
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    (∫ y, |empiricalMean (k := k) (π.normalizedGameKernel lam) y-normalizedScalarGap P lam|
      ∂P.trainingCoordinateLaw k) ≤
      Real.sqrt (pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*
        (P.optimalScalarRatio-optimalCompetitiveRatio)/(k : ℝ) + 1/(k : ℝ)^2) := by
  let f := π.normalizedGameKernel lam
  let ν := P.trainingCoordinateLaw k
  let c := ∫ x, f x ∂P.valuesLaw
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1, by linarith [hlam.2]⟩
  have hf := π.measurable_normalizedGameKernel lam
  have hb := π.normalizedGameKernel_abs_le_ae P hcap hLam
  have hA := memLp_firstOrderEmpirical_of_ae_bounded (k := k) P.law hf 1 hb 2
  have hB := memLp_higherOrderEmpirical_of_ae_bounded (k := k) P.law hf 1 hb 2
  have he : empiricalMean (k := k) f = fun y => c+firstOrderEmpirical P.law f y+higherOrderEmpirical P.law f y :=
    funext (empiricalMean_order_decomposition P.law f)
  have hLp : MemLp (empiricalMean (k := k) f) 2 ν := by
    rw [he]
    exact ((memLp_const c).add hA).add hB
  have hMean := π.integral_empiricalGameKernel (k := k) P hcap hLam hOpt
  have hVar := π.empiricalGameKernel_variance_le_ratioSlack (k := k) P hP hcap hM hδ hlam hmin hOpt
  have hM2 : (∫ y, (empiricalMean (k := k) f y-normalizedScalarGap P lam)^2 ∂ν) ≤
      pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*
        (P.optimalScalarRatio-optimalCompetitiveRatio)/(k : ℝ) + 1/(k : ℝ)^2 := by
    rw [variance_eq_integral (measurable_empiricalMean hf).aemeasurable, hMean] at hVar
    exact hVar
  have hAbsM2 : (∫ y, |empiricalMean (k := k) f y-normalizedScalarGap P lam|^2 ∂ν) ≤
      pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*
        (P.optimalScalarRatio-optimalCompetitiveRatio)/(k : ℝ) + 1/(k : ℝ)^2 := by
    simpa only [sq_abs] using hM2
  have h := ProphetSecretary.Probability.abs_integral_le_sqrt_secondMoment ν
    (fun y => |empiricalMean (k := k) f y-normalizedScalarGap P lam|)
    (hLp.sub (memLp_const (normalizedScalarGap P lam))).abs hAbsM2
  rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at h
  exact h

end ProphetSecretary.Model
