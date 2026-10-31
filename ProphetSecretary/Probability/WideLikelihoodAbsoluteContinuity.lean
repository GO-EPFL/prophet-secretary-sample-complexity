import ProphetSecretary.Probability.WideLikelihoodPath

/-!
# Absolute continuity on the manuscript's likelihood interval

The original product-density identity supplies the actual changed law. Product
independence then transfers null events while retaining independent arrival
clocks and auxiliary policy randomness.
-/

open MeasureTheory

namespace ProphetSecretary.Model.Instance

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma likelihoodWidePath_valuesLaw_absolutelyContinuous_quarter (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1)
    (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (P.likelihoodWidePath h hh hb hm θ).valuesLaw ≪ P.valuesLaw := by
  rw [P.likelihoodWidePath_eq_quarter h hh hb hm hθ, P.likelihoodPath_of_mem h hh hb hm hθ,
    P.likelihoodTilt_valuesLaw h hh hb hm θ hθ]
  exact withDensity_absolutelyContinuous _ _

lemma likelihoodWidePath_worldLaw_absolutelyContinuous_quarter (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1)
    (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (P.likelihoodWidePath h hh hb hm θ).worldLaw ν ≪ P.worldLaw ν := by
  exact (P.likelihoodWidePath_valuesLaw_absolutelyContinuous_quarter h hh hb hm hθ).prod .rfl

end ProphetSecretary.Model.Instance
