import ProphetSecretary.Statistics.KernelLikelihoodResponse
import ProphetSecretary.Statistics.FirstProjectionDirection
import ProphetSecretary.Analysis.InformationSlopeBound
import ProphetSecretary.Statistics.Hoeffding.AlmostSureBound

/-!
# First-projection variance near a small scalar gap

This is `eq:bayes-first-projection`. The policy is optimal at the fixed base
law and fixed scalar. Its actual first projections construct the likelihood
direction. Uniform law curvature and nonnegativity give the bound with an
explicit constant chosen before the instance size and laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability ProphetSecretary.Analysis

noncomputable def pilotFirstProjectionConstant (δ : ℝ) : ℝ :=
  16*(lawCurvatureConstant 1 δ+8+1)

lemma pilotFirstProjectionConstant_positive {δ : ℝ} (hδ : 0 < δ) :
    0 < pilotFirstProjectionConstant δ := by
  have hC := lawCurvatureConstant_nonnegative zero_le_one hδ
  unfold pilotFirstProjectionConstant
  positivity

variable {n : ℕ}

theorem RandomizedPolicy.firstProjection_variance_le_normalizedGap (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ))
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    P.firstProjectionVariance (π.normalizedGameKernel lam) ≤
      pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*normalizedScalarGap P lam := by
  have hLam : lam ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith only [hlam.2,hδ]⟩
  have hLam01 : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1.le,hLam.2.le⟩
  let f := π.normalizedGameKernel lam
  have hf : Measurable f := π.measurable_normalizedGameKernel lam
  have hfB : ∀ᵐ x ∂P.valuesLaw, |f x| ≤ 1 := π.normalizedGameKernel_abs_le_ae P hcap ⟨hLam.1,hLam.2.le⟩
  let h := P.firstProjectionDirection f
  have hh i : Measurable (h i) := P.measurable_firstProjectionDirection hf i
  have hb i : ∀ᵐ a ∂P.law i, |h i a| ≤ 1 := P.firstProjectionDirection_abs_le_ae hf hfB i
  have hm i : (∫ a, h i a ∂P.law i) = 0 := P.integral_firstProjectionDirection hf hfB i
  let F := fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam
  let K := lawCurvatureConstant 1 δ+8
  have hK : 0 ≤ K := add_nonneg (lawCurvatureConstant_nonnegative zero_le_one hδ) (by norm_num)
  have hI := information_nonnegative P.law h
  have hF0 : F 0 = normalizedScalarGap P lam := by
    dsimp only [F]
    rw [P.likelihoodWidePath_zero_eq h hh hb hm]
  have hNonneg (t : ℝ) (_ht : t ∈ Icc (-(1/4) : ℝ) (1/4)) : 0 ≤ F t :=
    normalizedScalarGap_nonnegative _ ((P.likelihoodWidePath h hh hb hm t).integrable_maximum_of_bounded
      (P.likelihoodWidePath_bounded h hh hb hm t hcap)) hLam01
  have hD0 : deriv F 0 = -2*information P.law h :=
    (π.deriv_normalizedGap_eq_kernelScore_of_opt P hcap hLam hOpt h hh hb hm).trans
      (P.integral_kernel_firstProjectionDirection_eq_information hf hfB)
  have hLip : ∀ t ∈ Icc (-(1/4) : ℝ) (1/4), ∀ u ∈ Icc (-(1/4) : ℝ) (1/4),
      |deriv F u-deriv F t| ≤ (K*(1+P.totalFirstMoment)*information P.law h)*|u-t| := by
    intro t ht u hu
    simpa only [mul_one] using P.lawGap_deriv_lipschitz_uniform zero_le_one hδ hlam hcap h hh hb hm ht hu
  have hBound := information_le_of_nonnegative_smooth hK P.totalFirstMoment_nonnegative hI
    hNonneg (fun t ht => P.hasDerivAt_normalizedGap_wide hcap hLam h hh hb hm ht) hLip hD0
  rw [hF0] at hBound
  calc
    P.firstProjectionVariance f = 4*information P.law h := by
      rw [P.information_firstProjectionDirection]
      ring
    _ ≤ 4*(4*(K+1)*(1+P.totalFirstMoment)*normalizedScalarGap P lam) :=
      mul_le_mul_of_nonneg_left hBound (by norm_num)
    _ = _ := by unfold pilotFirstProjectionConstant; dsimp only [K]; ring

/-- Existence is supplied by the proved canonical optimizer, rather than an
extra hypothesis on an unknown policy. -/
theorem Instance.exists_optimal_policy_with_firstProjection_bound (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ)) :
    ∃ π : RandomizedPolicy n, π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam) ∧
      P.firstProjectionVariance (π.normalizedGameKernel lam) ≤
        pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*normalizedScalarGap P lam := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hw : 0 < lam := hδ.trans_le hlam.1
  have hc : 0 ≤ 1-lam := by linarith only [hlam.2,hδ]
  let π := P.valuePolicy hP hw.le hc
  have hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam) := P.valuePolicy_optimal hP hw hc
  exact ⟨π,hOpt,π.firstProjection_variance_le_normalizedGap P hcap hδ hlam hOpt⟩

/-- The actual independent first-order training sum has the gap-dependent
variance needed for the fixed-weight Bernstein bound. -/
theorem RandomizedPolicy.firstOrder_sample_variance_le_normalizedGap {k : ℕ} [NeZero k]
    (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ))
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    variance (fun y : (Fin n × Fin k) → ℝ => (k : ℝ)⁻¹*∑ q : Fin n × Fin k,
      ProphetSecretary.Probability.Hoeffding.firstProjection P.law (π.normalizedGameKernel lam) q.1 (y q))
      (P.trainingCoordinateLaw k) ≤
        pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*normalizedScalarGap P lam/(k : ℝ) := by
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith only [hlam.2,hδ]⟩
  have hf := π.measurable_normalizedGameKernel lam
  have hb := π.normalizedGameKernel_abs_le_ae P hcap hLam
  have heq := ProphetSecretary.Statistics.Hoeffding.variance_firstOrder_sample_sum (k := k) P.law hf 1 hb
  change variance _ (Measure.pi (fun q : Fin n × Fin k => P.law q.1)) ≤ _
  rw [heq]
  have h := mul_le_mul_of_nonneg_left (π.firstProjection_variance_le_normalizedGap P hcap hδ hlam hOpt)
    (inv_nonneg.mpr (Nat.cast_nonneg k))
  exact h.trans_eq (by ring)

end ProphetSecretary.Model
