import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Analysis.NonnegativeSmoothSlope

/-!
# Uniform law derivatives of nonnegative scalar gaps and regrets

The optimized gap and fixed-policy regret are different functions. Each has
nonnegative values on the common quarter perturbation interval. The actual
curvature bounds give explicit square-root control at zero, including zero gap.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n : ℕ}

noncomputable def smoothEnvelopeCurvatureConstant (H S₀ δ I₀ : ℝ) : ℝ :=
  (lawCurvatureConstant H δ + 8 * (H+1)) * (1+S₀) * I₀
noncomputable def smoothEnvelopeSlopeConstant (H S₀ δ I₀ : ℝ) : ℝ :=
  Real.sqrt (8 * smoothEnvelopeCurvatureConstant H S₀ δ I₀ + 64 * (H+1) + 2)

lemma Instance.normalizedScalarValue_le_cap_add_one (P : Instance n) {H lam : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    optimalScalarValue P lam (1-lam) ≤ H+1 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hv := optimalScalarValue_le_benchmark P hP hlam.1 (sub_nonneg.mpr hlam.2)
  have hM := P.expectedMaximum_le_of_bounded hH hbound
  have hm := mul_le_mul_of_nonneg_left hM hlam.1
  have hHlam := mul_le_mul_of_nonneg_right hlam.2 hH
  nlinarith only [hv,hm,hHlam,hlam.1]

/-- Both actual derivatives have one constant selected before the finite
instance and the fixed policy. -/
theorem RandomizedPolicy.lawGap_regret_derivative_sqrt_bounds (π : RandomizedPolicy n) (P : Instance n)
    {H S₀ δ I₀ lam : ℝ} (hH : 0 ≤ H) (hS₀ : 0 ≤ S₀) (hδ : 0 < δ) (hI₀ : 0 ≤ I₀)
    (hlam : lam ∈ Icc δ (1-δ)) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (hS : P.totalFirstMoment ≤ S₀)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (hInfo : information P.law h ≤ I₀) :
    |deriv (fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) 0| ≤
      smoothEnvelopeSlopeConstant H S₀ δ I₀ * Real.sqrt (normalizedScalarGap P lam) ∧
    |deriv (fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam) 0| ≤
      smoothEnvelopeSlopeConstant H S₀ δ I₀ * Real.sqrt (π.normalizedRegret P lam) := by
  let F : ℝ → ℝ := fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam
  let G : ℝ → ℝ := fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam
  let C₀ := lawCurvatureConstant H δ + 8 * (H+1)
  let Q := smoothEnvelopeCurvatureConstant H S₀ δ I₀
  have hlam' : lam ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith [hlam.2]⟩
  have hlam01 : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam'.1.le,hlam'.2.le⟩
  have hP := P.integrable_maximum_of_bounded hbound
  have hSpos := P.totalFirstMoment_nonnegative
  have hI := information_nonnegative P.law h
  have hC₀ : 0 ≤ C₀ := add_nonneg (lawCurvatureConstant_nonnegative hH hδ) (by positivity)
  have hQ : 0 ≤ Q := by dsimp [Q,smoothEnvelopeCurvatureConstant]; positivity
  have hcurrent : C₀ * (1+P.totalFirstMoment) * information P.law h ≤ Q := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hS] : 1+P.totalFirstMoment ≤ 1+S₀) hC₀)
      hInfo hI (mul_nonneg hC₀ (by positivity))
  have hFcurrent : (lawCurvatureConstant H δ + 8 * H) * (1+P.totalFirstMoment) * information P.law h ≤ Q := by
    have hbase : lawCurvatureConstant H δ + 8 * H ≤ C₀ := by dsimp [C₀]; linarith
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ 1+P.totalFirstMoment)) hI).trans hcurrent
  have hF0 : F 0 = normalizedScalarGap P lam := by
    change normalizedScalarGap (P.likelihoodWidePath h hh hb hm 0) lam = _
    rw [P.likelihoodWidePath_zero_eq h hh hb hm]
  have hG0 : G 0 = π.normalizedRegret P lam := by
    change π.normalizedRegret (P.likelihoodWidePath h hh hb hm 0) lam = _
    rw [P.likelihoodWidePath_zero_eq h hh hb hm]
  have hFnonneg (t : ℝ) (_ht : t ∈ Icc (-(1/4) : ℝ) (1/4)) : 0 ≤ F t :=
    normalizedScalarGap_nonnegative _ ((P.likelihoodWidePath h hh hb hm t).integrable_maximum_of_bounded
      (P.likelihoodWidePath_bounded h hh hb hm t hbound)) hlam01
  have hGnonneg (t : ℝ) (_ht : t ∈ Icc (-(1/4) : ℝ) (1/4)) : 0 ≤ G t :=
    π.normalizedRegret_nonnegative _ ((P.likelihoodWidePath h hh hb hm t).integrable_maximum_of_bounded
      (P.likelihoodWidePath_bounded h hh hb hm t hbound)) hlam01
  have hVbound := P.normalizedScalarValue_le_cap_add_one hH hbound hlam01
  have hFbase : F 0 ≤ H+1 := by
    rw [hF0]
    have hb0 : 0 ≤ optimalCompetitiveRatio * (lam * P.expectedMaximum + (1-lam)) :=
      mul_nonneg optimalCompetitiveRatio_nonnegative
        (add_nonneg (mul_nonneg hlam01.1 P.expectedMaximum_nonnegative) (sub_nonneg.mpr hlam01.2))
    unfold normalizedScalarGap scalarGap
    linarith only [hVbound,hb0]
  have hGbase : G 0 ≤ H+1 := by
    rw [hG0]
    have hj := π.scalarObjective_nonnegative P hP hlam01.1 (sub_nonneg.mpr hlam01.2)
    unfold RandomizedPolicy.normalizedRegret
    linarith only [hVbound,hj]
  have hFd (t : ℝ) (ht : t ∈ Icc (-(1/4) : ℝ) (1/4)) : HasDerivAt F (deriv F t) t := by
    have hHalf : t ∈ Ioo (-(1/2) : ℝ) (1/2) := by constructor <;> linarith [ht.1,ht.2]
    have hv := (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hlam'.1 (sub_pos.mpr hlam'.2)
      hH hbound h hh hb hm hHalf).differentiableAt
    have hM := (P.expectedMaximum_likelihoodWidePath_twice_differentiable hH hbound h hh hb hm hHalf).1
    exact (hv.sub (((hM.const_mul lam).add_const (1-lam)).const_mul optimalCompetitiveRatio)).hasDerivAt
  have hGd (t : ℝ) (ht : t ∈ Icc (-(1/4) : ℝ) (1/4)) : HasDerivAt G (deriv G t) t :=
    (π.hasDerivAt_normalizedRegret_likelihoodWidePath P hH hlam' hbound h hh hb hm ht).differentiableAt.hasDerivAt
  have hFlip : ∀ t ∈ Icc (-(1/4) : ℝ) (1/4), ∀ s ∈ Icc (-(1/4) : ℝ) (1/4),
      |deriv F s - deriv F t| ≤ Q * |s-t| := by
    intro t ht s hs
    exact (P.lawGap_deriv_lipschitz_uniform hH hδ hlam hbound h hh hb hm ht hs).trans
      (mul_le_mul_of_nonneg_right hFcurrent (abs_nonneg _))
  have hGlip : ∀ t ∈ Icc (-(1/4) : ℝ) (1/4), ∀ s ∈ Icc (-(1/4) : ℝ) (1/4),
      |deriv G s - deriv G t| ≤ Q * |s-t| := by
    intro t ht s hs
    exact (π.lawRegret_deriv_lipschitz P hH hδ hlam hbound h hh hb hm ht hs).trans
      (mul_le_mul_of_nonneg_right hcurrent (abs_nonneg _))
  have hF := nonnegative_derivative_le_sqrt (by positivity : 0 ≤ H+1) hQ hFbase hFnonneg hFd hFlip
  have hG := nonnegative_derivative_le_sqrt (by positivity : 0 ≤ H+1) hQ hGbase hGnonneg hGd hGlip
  rw [hF0] at hF
  rw [hG0] at hG
  exact ⟨hF,hG⟩

end ProphetSecretary.Model
