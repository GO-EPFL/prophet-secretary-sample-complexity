import ProphetSecretary.Stability.LawNormalizedRegularity
import ProphetSecretary.Probability.WideFixedPolicyRegularity
import ProphetSecretary.Probability.WideMaximumRegularity

/-! # `upfish:curvature`: finite product laws
The directional argument applies directly to arbitrary bounded marginal laws.
The wider half-interval extension agrees with the manuscript's actual likelihood
laws throughout its closed quarter interval. Constants are explicit functions of
the cap and coefficient ranges, before the instance and scores are selected.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n : ℕ}

/-- Optimized-value and integrated curvature clauses of `upfish:curvature`. -/
theorem Instance.law_curvature (P : Instance n) {H W C δ w c : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hw : 0 < w) (hwW : w ≤ W)
    (hc : 0 < c) (hcC : c ≤ C) (hδc : δ ≤ c)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    let f := fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c
    let K := lawCoefficientRangeConstant H W C δ * (1 + P.totalFirstMoment) * information P.law h
    (∀ θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4), DifferentiableAt ℝ f θ) ∧
      (∀ θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ∀ ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        |deriv f ρ - deriv f θ| ≤ K * |ρ - θ|) ∧
      (∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)), |deriv (deriv f) θ| ≤ K) := by
  have hCoef := lawCurvatureCoefficient_range_le hH hδ hw.le hwW hc hcC hδc P.totalFirstMoment_nonnegative
  have hI := information_nonnegative P.law h
  refine ⟨(P.lawValue_uniform_C11 hw hc hH hbound h hh hb hm).1, ?_, ?_⟩
  · intro θ hθ ρ hρ
    exact (P.lawValue_deriv_lipschitz_information hw hc hH hbound h hh hb hm hθ hρ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoef hI) (abs_nonneg _))
  · filter_upwards [P.lawValue_secondDerivative_bound_ae hw hc hH hbound h hh hb hm] with θ hθ
    exact hθ.trans (mul_le_mul_of_nonneg_right hCoef hI)

/-- The extension supplies the original perturbed instance at every manuscript parameter. -/
lemma Instance.law_curvature_model_transfer (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    P.likelihoodWidePath h hh hb hm θ = P.likelihoodTilt h hh hb hm θ hθ := by
  rw [P.likelihoodWidePath_eq_quarter h hh hb hm hθ, P.likelihoodPath_of_mem h hh hb hm hθ]

/-- Fixed-policy clause, with the same observer and seed law on the entire curve. -/
theorem RandomizedPolicy.law_curvature (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    (∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      |deriv (deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c)) θ| ≤
        8 * (w * H + c) * information P.law h) ∧
      (∀ θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ∀ ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        |deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) ρ -
          deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
          (8 * (w * H + c) * information P.law h) * |ρ - θ|) :=
  ⟨π.fixedLaw_secondDerivative_bound_ae P hw hc hH hbound h hh hb hm,
    fun _ hθ _ hρ ↦ π.fixedLaw_deriv_lipschitz_information P hw hc hH hbound h hh hb hm hθ hρ⟩


/-- Benchmark clause of `upfish:curvature`, including endpoint derivatives of
its actual half-neighborhood extension. -/
theorem Instance.maximum_law_curvature (P : Instance n) {H : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      let M := fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum
      DifferentiableAt ℝ M θ ∧ DifferentiableAt ℝ (deriv M) θ ∧
        |deriv (deriv M) θ| ≤ 8 * H * information P.law h := by
  intro θ hθ
  exact P.expectedMaximum_likelihoodWidePath_twice_differentiable hH hbound h hh hb hm
    (show θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) by constructor <;> linarith [hθ.1, hθ.2])

end ProphetSecretary.Model
