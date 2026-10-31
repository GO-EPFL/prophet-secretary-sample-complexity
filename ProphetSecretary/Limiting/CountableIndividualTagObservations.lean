import ProphetSecretary.Limiting.CountableSeededIndividualPullback
import ProphetSecretary.Limiting.CountableSeedTransport

/-!
# Revealing one independent tag at its individual occurrence

An independent tag may influence the decision at its own arrival and every
later decision. Before that arrival, changing the tag leaves both callbacks
unchanged. Presence is tested on the history entry, so an observed zero also
reveals the tag.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed T : Type*}

/-- Nonanticipation of a latent occurrence tag, additional to the ordinary
observable-history restriction of `CountableRule`. -/
def CountableRule.TagBlindBefore (π : CountableRule (Seed × T)) (i : ℕ) : Prop :=
  (∀ r σ σ' t j x H ξ, j≠i → H i=none →
    π.individual (r,σ) t j x H ξ=π.individual (r,σ') t j x H ξ) ∧
  (∀ r σ σ' t x H ξ, H i=none →
    π.poisson (r,σ) t x H ξ=π.poisson (r,σ') t x H ξ)

lemma CountableRule.comapSeed_tagBlindBefore (π : CountableRule Seed) (i : ℕ) :
    (π.comapSeed (Prod.fst : Seed × T → Seed)).TagBlindBefore i := by
  constructor <;> intros <;> rfl

lemma mapSingleIndividualHistory_eq_of_none (i : ℕ) (g : ℝ → ℝ) (H : IndividualHistory) (hH : H i=none) :
    mapSingleIndividualHistory i g H=H := by
  funext j
  by_cases hj : j=i
  · subst j
    simp only [mapSingleIndividualHistory,if_true,hH,Model.mapObservationValues]
  · exact if_neg hj

lemma CountableRule.pullbackSeededIndividual_tagBlindBefore (π : CountableRule Seed) (i : ℕ)
    (g : Seed × T → ℝ → ℝ) :
    ((π.comapSeed Prod.fst).pullbackSeededIndividual i g).TagBlindBefore i := by
  constructor
  · intro r σ σ' t j x H ξ hji hH
    simp only [CountableRule.pullbackSeededIndividual,if_neg hji,mapSingleIndividualHistory_eq_of_none i _ H hH,
      CountableRule.comapSeed]
  · intro r σ σ' t x H ξ hH
    simp only [CountableRule.pullbackSeededIndividual,mapSingleIndividualHistory_eq_of_none i _ H hH,
      CountableRule.comapSeed]

end ProphetSecretary.Limiting.CountableInstance
