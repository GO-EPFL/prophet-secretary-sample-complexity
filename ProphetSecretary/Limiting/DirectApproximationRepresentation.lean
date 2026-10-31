import ProphetSecretary.Limiting.FinitePoissonApproximation
import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Model.StandbyIidReward
import ProphetSecretary.Model.Continuation

/-!
# Exact product representation of the finite Poisson design

The retained identities precede the virtual iid identities. This is equality
of the actual finite marginal laws, including every zero-valued identity;
no policy observation or random variable is removed.
-/
open MeasureTheory Set
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma finitePoissonDesign_eq_appendIndependent_iid (P : Model.Instance n) (κ : Measure ℝ)
    [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0≤x) (p : unitInterval) (N : ℕ) :
    finitePoissonDesign P κ hκ p N=P.appendIndependent
      (Model.iidOfferInstance (zeroInflatedLaw κ p) (zeroInflatedLaw_nonnegative κ hκ p) N) := by
  apply Model.Instance.eq_of_law_eq
  rfl

lemma FiniteIntensityHybridInstance.finitePoissonApproximation_eq_appendIndependent_iid
    (B : FiniteIntensityHybridInstance n) (j : ℕ) :
    B.finitePoissonApproximation j=B.individuals.appendIndependent
      (Model.iidOfferInstance
        (zeroInflatedLaw (normalizedMarkOrZero B.intensity)
          (bernoulliProbability ((B.intensity:Measure ℝ).real univ) measureReal_nonneg j))
        (zeroInflatedLaw_nonnegative _
          ((normalizedMarkOrZero_bounds B.intensity B.cap.property B.intensity_supported).mono (fun _ hx => hx.1)) _)
        (bernoulliMultiplicity ((B.intensity:Measure ℝ).real univ) j)) := by
  apply Model.Instance.eq_of_law_eq
  rfl
end ProphetSecretary.Limiting
