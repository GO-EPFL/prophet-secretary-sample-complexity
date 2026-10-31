import ProphetSecretary.Analysis.PointwiseDerivativeRegularity
import ProphetSecretary.Probability.NormalizedScoreResponse

/-!
# Fixed-policy score limits from actual perturbed policy means

Each finite policy and its independent auxiliary law are fixed while the
likelihood parameter varies. Pointwise convergence on a common neighborhood,
together with the proved dimension-independent derivative Lipschitz bound,
forces convergence of complete-score expectations. Base value convergence
alone is not used. No total-first-moment bound is required.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis

theorem expectedScalarScore_tendsto_of_perturbed_policy_means
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (π : ∀ m, RandomizedPolicy (sizes m))
    {H I w c : ℝ} (hH : 0≤H) (hI : 0≤I) (hw : 0≤w) (hc : 0≤c)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (F : ℝ → ℝ) {D : ℝ} (hF : HasDerivAt F D 0)
    (hLimit : ∀ θ∈Icc (-(1/4):ℝ) (1/4), Tendsto
      (fun m => (π m).scalarObjective
        ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ) w c) atTop (𝓝 (F θ))) :
    Tendsto (fun m => w*(π m).expectedRewardScore (P m) (score m)+
      c*(π m).expectedDurationScore (P m) (score m)) atTop (𝓝 D) := by
  let f := fun m θ => (π m).scalarObjective
    ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ) w c
  let g := fun m θ => deriv (f m) θ
  let K : ℝ≥0 := ⟨8*(w*H+c)*I,by positivity⟩
  have hDeriv (m θ) (hθ : θ∈Icc (-(1/4):ℝ) (1/4)) : HasDerivAt (f m) (g m θ) θ := by
    have hHalf : θ∈Ioo (-(1/2):ℝ) (1/2) := by constructor <;> linarith only [hθ.1,hθ.2]
    exact ((π m).hasDerivAt_scalarObjective_likelihoodWidePath (P m) hw hc hH (hCap m)
      (score m) (hh m) (hb m) (hm m) hHalf).differentiableAt.hasDerivAt
  have hLip (m) : LipschitzOnWith K (g m) (Icc (-(1/4):ℝ) (1/4)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := (π m).fixedLaw_deriv_lipschitz_information (P m) hw hc hH (hCap m)
      (score m) (hh m) (hb m) (hm m) hy hx
    have hK : 8*(w*H+c)*information (P m).law (score m)≤(K:ℝ) :=
      mul_le_mul_of_nonneg_left (hInfo m) (by positivity)
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
  have h := ((π m).hasDerivAt_scalarObjective_likelihoodWidePath_zero (P m) hH (hCap m)
    hw hc (score m) (hh m) (hb m) (hm m)).deriv
  rw [(π m).scalarLikelihoodDerivative_eq_scores (P m) hH (hCap m) (score m) (hh m) (hb m)] at h
  exact h

end ProphetSecretary.Model
