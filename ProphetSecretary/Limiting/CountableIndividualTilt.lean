import ProphetSecretary.Limiting.CountableIndividualChange
import ProphetSecretary.Probability.InfiniteCoordinateDensity
import ProphetSecretary.Probability.LikelihoodTilt
import ProphetSecretary.Limiting.CountableObservations

/-!
# Actual individual likelihood tilts of the full independent instance

Only one value law changes. Every identity, independent arrival clock,
anonymous intensity and independent policy seed remains in the model. The
complete-world density depends on that value even if it arrives after stopping;
it is an analytical likelihood, not an additional policy observation.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def individualLikelihoodTilt (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) (hθ : |θ| ≤ 1/4) : CountableInstance :=
  B.updateIndividual i
    ⟨ProphetSecretary.Probability.tiltLaw (B.individuals i : Measure ℝ) h θ,
      ProphetSecretary.Probability.tiltLaw_probability hh hb hm hθ⟩
    ((ProphetSecretary.Probability.tiltLaw_absolutelyContinuous (B.individuals i : Measure ℝ) h θ).ae_le
      (B.individual_supported i))

noncomputable def individualLikelihoodPath (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) : CountableInstance :=
  if hθ : |θ| ≤ 1/4 then B.individualLikelihoodTilt i h hh hb hm θ hθ else B

lemma individualLikelihoodPath_of_mem (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    B.individualLikelihoodPath i h hh hb hm θ=B.individualLikelihoodTilt i h hh hb hm θ hθ :=
  dif_pos hθ

lemma individualLikelihoodPath_zero (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    B.individualLikelihoodPath i h hh hb hm 0=B := by
  rw [B.individualLikelihoodPath_of_mem i h hh hb hm (by norm_num : |(0 : ℝ)| ≤ 1/4)]
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · funext j
    by_cases hji : j=i
    · subst j
      change (Function.update B.individuals i _ i)=B.individuals i
      rw [Function.update_self]
      apply Subtype.ext
      simp [ProphetSecretary.Probability.tiltLaw,ProphetSecretary.Probability.tiltFactor]
    · change (Function.update B.individuals i _ j)=B.individuals j
      exact Function.update_of_ne hji _ _
  · rfl

lemma individualLikelihoodTilt_valuesLaw (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) (hθ : |θ| ≤ 1/4) :
    (B.individualLikelihoodTilt i h hh hb hm θ hθ).individualValuesLaw=
      ProphetSecretary.Probability.tiltLaw B.individualValuesLaw (fun x => h (x i)) θ := by
  let μ := fun j : ℕ => (B.individuals j : Measure ℝ)
  let f := fun x => ENNReal.ofReal (ProphetSecretary.Probability.tiltFactor h θ x)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (ProphetSecretary.Probability.measurable_tiltFactor hh θ)
  haveI : IsProbabilityMeasure ((μ i).withDensity f) :=
    ProphetSecretary.Probability.tiltLaw_probability hh hb hm hθ
  have hMarginals : (fun j => ((B.individualLikelihoodTilt i h hh hb hm θ hθ).individuals j : Measure ℝ))=
      Function.update μ i ((μ i).withDensity f) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp only [individualLikelihoodTilt,updateIndividual,Function.update_self,μ,f,
        ProphetSecretary.Probability.tiltLaw]
      rfl
    · simp only [individualLikelihoodTilt,updateIndividual,Function.update_of_ne hji,μ]
  change Measure.infinitePi _=_
  rw [hMarginals,ProphetSecretary.Probability.infinitePi_update_withDensity μ i f hf]
  rfl

lemma individualLikelihoodTilt_completeWorldLaw (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) (hθ : |θ| ≤ 1/4)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.individualLikelihoodTilt i h hh hb hm θ hθ).completeWorldLaw ν=
      ProphetSecretary.Probability.tiltLaw (B.completeWorldLaw ν) (fun v => h (v.2.1 i)) θ := by
  let f := fun x : ℕ → ℝ => ENNReal.ofReal (ProphetSecretary.Probability.tiltFactor h θ (x i))
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    ((ProphetSecretary.Probability.measurable_tiltFactor hh θ).comp (measurable_pi_apply i))
  change B.bandConfigurationsLaw.prod
    ((B.individualLikelihoodTilt i h hh hb hm θ hθ).individualValuesLaw.prod (individualClocksLaw.prod ν))=_
  rw [B.individualLikelihoodTilt_valuesLaw i h hh hb hm θ hθ]
  change B.bandConfigurationsLaw.prod
    ((B.individualValuesLaw.withDensity f).prod (individualClocksLaw.prod ν))=_
  rw [prod_withDensity_left hf]
  change B.bandConfigurationsLaw.prod
    ((B.individualValuesLaw.prod (individualClocksLaw.prod ν)).withDensity (f ∘ Prod.fst))=_
  rw [prod_withDensity_right (hf.comp measurable_fst)]
  rfl

end ProphetSecretary.Limiting.CountableInstance
