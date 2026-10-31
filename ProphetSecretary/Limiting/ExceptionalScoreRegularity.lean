import ProphetSecretary.Limiting.ScoreLiftLikelihoodRegularity
import ProphetSecretary.Probability.ScoreArrayMask

/-!
# Uniform curvature when exceptional scalar indices have zero perturbation

A compact replacement weight may differ at finitely many initial indices.
Zero scores make the actual law constant at those indices, so curvature
vanishes there even if the original normalized weight is an endpoint.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

theorem finite_score_likelihood_regularity_of_exceptional_weights
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H S0 I δ : ℝ}
    (hH : 0≤H) (hS0 : 0≤S0) (hI : 0≤I) (hδ : 0<δ)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hMeas : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (ls lams : ℕ → ℝ) (hLs : ∀ m, ls m∈Icc δ (1-δ))
    (hOff : ∀ m, ls m≠lams m → ∀ i x, score m i x=0) :
    (∀ m θ, |θ|≤1/4 →
      information ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ).law
        (fun i => tiltedScore (score m i) θ)≤(4/3)*I) ∧
    (∀ m θ, |θ|≤1/4 →
      ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ).totalFirstMoment≤(5/4)*S0) ∧
    (∀ m,
      let f := fun θ => optimalScalarValue ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ) (lams m) (1-lams m)
      let K := lawCoefficientRangeConstant H 1 1 δ*(1+S0)*I
      (∀ θ∈Icc (-(1/4):ℝ) (1/4), DifferentiableAt ℝ f θ) ∧
      (∀ θ∈Icc (-(1/4):ℝ) (1/4), ∀ ρ∈Icc (-(1/4):ℝ) (1/4),
        |deriv f ρ-deriv f θ|≤K*|ρ-θ|) ∧
      (∀ᵐ θ ∂volume.restrict (Ioo (-(1/4):ℝ) (1/4)), |deriv (deriv f) θ|≤K)) := by
  have h := finite_score_likelihood_regularity sizes P hH hS0 hI hδ hCap hS score hMeas hBound hMean hInfo
  refine ⟨h.1,h.2.1,?_⟩
  intro m
  by_cases he : ls m=lams m
  · simpa only [he] using h.2.2 m (ls m) (hLs m)
  · have hPath (θ : ℝ) := (P m).likelihoodWidePath_eq_self_of_zero (score m) (hMeas m) (hBound m) (hMean m)
      (hOff m he) θ
    have hFamily : (fun θ => optimalScalarValue ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ)
        (lams m) (1-lams m))=(fun _ : ℝ => optimalScalarValue (P m) (lams m) (1-lams m)) := by
      funext θ
      exact congrArg (fun Q : Instance (sizes m) => optimalScalarValue Q (lams m) (1-lams m)) (hPath θ)
    have hK : 0≤lawCoefficientRangeConstant H 1 1 δ*(1+S0)*I := by
      unfold lawCoefficientRangeConstant
      positivity
    dsimp only
    rw [hFamily]
    simp only [deriv_const',sub_self,abs_zero]
    exact ⟨fun _ _ => differentiableAt_const _,fun _ _ _ _ => mul_nonneg hK (abs_nonneg _),
      Filter.Eventually.of_forall (fun _ => hK)⟩
end ProphetSecretary.Limiting
