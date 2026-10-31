import ProphetSecretary.Probability.LikelihoodRebase

/-! # Complete-world integration under a likelihood tilt
Only the offer marginals change. Clocks and auxiliary policy randomness retain
their independent laws, so the complete-world density depends on offers alone.
-/
open MeasureTheory
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma likelihoodTilt_worldLaw (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (P.likelihoodTilt h hh hb hm θ hθ).worldLaw ν =
      (P.worldLaw ν).withDensity (fun ω ↦ ENNReal.ofReal (likelihood h θ ω.1)) := by
  change (P.likelihoodTilt h hh hb hm θ hθ).valuesLaw.prod _ = _
  rw [P.likelihoodTilt_valuesLaw h hh hb hm θ hθ,
    prod_withDensity_left ((measurable_likelihood hh θ).ennreal_ofReal)]
  rfl

lemma integral_likelihoodTilt_worldLaw (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) (F : World n Seed → ℝ) :
    (∫ ω, F ω ∂(P.likelihoodTilt h hh hb hm θ hθ).worldLaw ν) =
      ∫ ω, likelihood h θ ω.1 * F ω ∂P.worldLaw ν := by
  have hL : Measurable (fun ω : World n Seed ↦ ENNReal.ofReal (likelihood h θ ω.1)) :=
    ((measurable_likelihood hh θ).comp measurable_fst).ennreal_ofReal
  rw [P.likelihoodTilt_worldLaw ν h hh hb hm hθ,
    integral_withDensity_eq_integral_toReal_smul hL
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  have hp : MeasurePreserving (fun ω : World n Seed ↦ ω.1) (P.worldLaw ν) P.valuesLaw := measurePreserving_fst
  filter_upwards [hp.quasiMeasurePreserving.ae (likelihood_ae_nonnegative P.law h hb hθ)] with ω hω
  rw [ENNReal.toReal_ofReal hω, smul_eq_mul]

end ProphetSecretary.Model.Instance
