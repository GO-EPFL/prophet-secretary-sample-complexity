import ProphetSecretary.Limiting.ExceptionalScoreRegularity
import ProphetSecretary.Limiting.ScoreLiftPayoffRegularity

/-!
# The complete uniform likelihood-regularity conclusion for lifted scores

All clauses refer to actual probability laws and actual derivatives. The
optimized-value, fixed-policy and benchmark clauses have separate constants.
The definition abbreviates this conclusion; the theorem constructs it from
centered bounded marginal scores with the proved information bound.
-/
open MeasureTheory Set
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

def UniformLikelihoodRegularity (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m))
    (Q : ∀ m, ℝ → Instance (sizes m)) (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
    (lams : ℕ → ℝ) (H S0 I δ : ℝ) : Prop :=
  (∀ m θ, |θ|≤1/4 → ∀ i, (Q m θ).law i=tiltLaw ((P m).law i) (score m i) θ) ∧
  (∀ m θ, |θ|≤1/4 → ∀ i, ∀ᵐ x ∂(Q m θ).law i, x≤H) ∧
  (∀ m θ, |θ|≤1/4 → information (Q m θ).law (fun i => tiltedScore (score m i) θ)≤(4/3)*I) ∧
  (∀ m θ, |θ|≤1/4 → (Q m θ).totalFirstMoment≤(5/4)*S0) ∧
  (∀ m, let f := fun θ => optimalScalarValue (Q m θ) (lams m) (1-lams m)
    let K := lawCoefficientRangeConstant H 1 1 δ*(1+S0)*I
    (∀ θ∈Icc (-(1/4):ℝ) (1/4), DifferentiableAt ℝ f θ) ∧
    (∀ θ∈Icc (-(1/4):ℝ) (1/4), ∀ ρ∈Icc (-(1/4):ℝ) (1/4), |deriv f ρ-deriv f θ|≤K*|ρ-θ|) ∧
    (∀ᵐ θ ∂volume.restrict (Ioo (-(1/4):ℝ) (1/4)), |deriv (deriv f) θ|≤K)) ∧
  (∀ m (π : RandomizedPolicy (sizes m)) lam, lam∈Icc (0:ℝ) 1 →
    let f := fun θ => π.scalarObjective (Q m θ) lam (1-lam)
    (∀ᵐ θ ∂volume.restrict (Ioo (-(1/4):ℝ) (1/4)), |deriv (deriv f) θ|≤8*(H+1)*I) ∧
    (∀ θ∈Icc (-(1/4):ℝ) (1/4), ∀ ρ∈Icc (-(1/4):ℝ) (1/4), |deriv f ρ-deriv f θ|≤(8*(H+1)*I)*|ρ-θ|)) ∧
  (∀ m θ, θ∈Icc (-(1/4):ℝ) (1/4) → let M := fun t => (Q m t).expectedMaximum
    DifferentiableAt ℝ M θ ∧ DifferentiableAt ℝ (deriv M) θ ∧ |deriv (deriv M) θ|≤8*H*I)

theorem score_lift_uniform_regularity
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H S0 I δ : ℝ}
    (hH : 0≤H) (hS0 : 0≤S0) (hI : 0≤I) (hδ : 0<δ)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hMeas : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (ls lams : ℕ → ℝ) (hLs : ∀ m, ls m∈Icc δ (1-δ))
    (hOff : ∀ m, ls m≠lams m → ∀ i x, score m i x=0) :
    UniformLikelihoodRegularity sizes P
      (fun m θ => (P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ)
      score lams H S0 I δ := by
  have h := finite_score_likelihood_regularity_of_exceptional_weights sizes P hH hS0 hI hδ hCap hS
    score hMeas hBound hMean hInfo ls lams hLs hOff
  exact ⟨fun m θ hθ i => (P m).likelihoodWidePath_law_quarter (score m) (hMeas m) (hBound m) (hMean m) hθ i,
    fun m θ _ => (P m).likelihoodWidePath_bounded (score m) (hMeas m) (hBound m) (hMean m) θ (hCap m),
    h.1,h.2.1,h.2.2,
    finite_score_fixedPolicy_curvature sizes P hH hI hCap score hMeas hBound hMean hInfo,
    finite_score_maximum_curvature sizes P hH hI hCap score hMeas hBound hMean hInfo⟩
end ProphetSecretary.Limiting
