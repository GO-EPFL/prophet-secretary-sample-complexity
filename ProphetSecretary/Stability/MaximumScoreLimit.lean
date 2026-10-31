import ProphetSecretary.Analysis.PointwiseDerivativeRegularity
import ProphetSecretary.Probability.NormalizedScoreResponse

/-!
# Maximum-score limits from actual perturbed benchmarks and uniform curvature

Pointwise convergence of the perturbed expected maxima is combined with the
proved information-dependent derivative Lipschitz estimate. The resulting
common quadratic remainder forces derivative convergence. Thus the complete
maximum-score expectation is not inferred from base value convergence alone.
No total-first-moment bound is used.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis

theorem expectedMaximumScore_tendsto_of_perturbed_benchmarks
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H I : ℝ} (hH : 0≤H) (hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (F : ℝ → ℝ) {D : ℝ} (hF : HasDerivAt F D 0)
    (hLimit : ∀ θ∈Icc (-(1/4):ℝ) (1/4), Tendsto
      (fun m => ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ).expectedMaximum) atTop (𝓝 (F θ))) :
    Tendsto (fun m => (P m).expectedMaximumScore (score m)) atTop (𝓝 D) := by
  let f := fun m θ => ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ).expectedMaximum
  let g := fun m θ => deriv (f m) θ
  let K : ℝ≥0 := ⟨8*H*I,by positivity⟩
  have hDeriv (m θ) (hθ : θ∈Icc (-(1/4):ℝ) (1/4)) : HasDerivAt (f m) (g m θ) θ := by
    have hHalf : θ∈Ioo (-(1/2):ℝ) (1/2) := by constructor <;> linarith only [hθ.1,hθ.2]
    exact ((P m).expectedMaximum_likelihoodWidePath_twice_differentiable hH (hCap m)
      (score m) (hh m) (hb m) (hm m) hHalf).1.hasDerivAt
  have hLip (m) : LipschitzOnWith K (g m) (Icc (-(1/4):ℝ) (1/4)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := (P m).expectedMaximum_likelihoodWidePath_deriv_lipschitz hH (hCap m)
      (score m) (hh m) (hb m) (hm m) hy hx
    have hK : 8*H*information (P m).law (score m)≤(K:ℝ) := mul_le_mul_of_nonneg_left (hInfo m) (by positivity)
    simpa only [Real.dist_eq] using h.trans (mul_le_mul_of_nonneg_right hK (abs_nonneg _))
  have hQuad (m z) (hz : z∈Icc (-(1/4):ℝ) (1/4)) (y) (hy : y∈Icc (-(1/4):ℝ) (1/4)) :
      |f m y-f m z-g m z*(y-z)|≤(K:ℝ)*(y-z)^2 :=
    quadratic_remainder_of_lipschitz_derivative (hDeriv m) (hLip m) hz hy
  have hx : (0:ℝ)∈Ioo (-(1/4):ℝ) (1/4) := by norm_num
  have hG := (cauchy_derivatives_of_quadratic K.property hx hQuad hLimit).tendsto_limUnder
  have hFD := hasDerivAt_pointwise_limit_of_quadratic K.property hx
    (fun m y hy => hQuad m 0 ⟨hx.1.le,hx.2.le⟩ y hy) hLimit hG
  have hEq := hFD.deriv.symm.trans hF.deriv
  rw [hEq] at hG
  apply hG.congr
  intro m
  exact ((P m).hasDerivAt_expectedMaximum_likelihoodWidePath_zero hH (hCap m)
    (score m) (hh m) (hb m) (hm m)).deriv
end ProphetSecretary.Model
