import ProphetSecretary.Limiting.CountableIndividualTilt
import ProphetSecretary.Limiting.CountableIndividualScore
import ProphetSecretary.Limiting.CountablePolicyLawTransport
import ProphetSecretary.Probability.SingleLikelihoodIntegral

/-!
# Actual policy payoffs along an individual likelihood path

The complete-world density gives mutual absolute continuity, hence the same
full class of observable stopping policies. The policy, its auxiliary law and
the scalar weights are fixed in every identity below. Reoptimization requires
a separate envelope theorem.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance

lemma individualLikelihoodTilt_absolutelyContinuous (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) (hθ : |θ| ≤ 1/4)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.individualLikelihoodTilt i h hh hb hm θ hθ).completeWorldLaw ν ≪ B.completeWorldLaw ν := by
  rw [B.individualLikelihoodTilt_completeWorldLaw i h hh hb hm θ hθ ν]
  exact ProphetSecretary.Probability.tiltLaw_absolutelyContinuous _ _ _

lemma absolutelyContinuous_individualLikelihoodTilt (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) (hθ : |θ| ≤ 1/4)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    B.completeWorldLaw ν ≪ (B.individualLikelihoodTilt i h hh hb hm θ hθ).completeWorldLaw ν := by
  rw [B.individualLikelihoodTilt_completeWorldLaw i h hh hb hm θ hθ ν]
  exact ProphetSecretary.Probability.tiltLaw_mutuallyAbsolutelyContinuous
    (measurable_individualScore i hh) (B.individualScore_bounded_ae ν i hb) hθ

lemma individualLikelihoodPath_absolutelyContinuous (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.individualLikelihoodPath i h hh hb hm θ).completeWorldLaw ν ≪ B.completeWorldLaw ν := by
  by_cases hθ : |θ| ≤ 1/4
  · rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ]
    exact B.individualLikelihoodTilt_absolutelyContinuous i h hh hb hm θ hθ ν
  · simp only [individualLikelihoodPath,dif_neg hθ]
    exact fun _ hs => hs

lemma absolutelyContinuous_individualLikelihoodPath (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    B.completeWorldLaw ν ≪ (B.individualLikelihoodPath i h hh hb hm θ).completeWorldLaw ν := by
  by_cases hθ : |θ| ≤ 1/4
  · rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ]
    exact B.absolutelyContinuous_individualLikelihoodTilt i h hh hb hm θ hθ ν
  · simp only [individualLikelihoodPath,dif_neg hθ]
    exact fun _ hs => hs

end CountableInstance

noncomputable def RandomizedCountablePolicy.individualLikelihoodPolicy {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) :
    RandomizedCountablePolicy (B.individualLikelihoodPath i h hh hb hm θ) :=
  π.changeInstance (B.individualLikelihoodPath i h hh hb hm θ)
    (B.individualLikelihoodPath_absolutelyContinuous i h hh hb hm θ π.seedLaw)

noncomputable def RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (w c : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ v, π.scalarPayoff w c v*h (v.2.1 i) ∂B.completeWorldLaw π.seedLaw

lemma RandomizedCountablePolicy.integrable_scalarIndividualLikelihood {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (w c : ℝ) {h : ℝ → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1) :
    Integrable (fun v => π.scalarPayoff w c v*h (v.2.1 i)) (B.completeWorldLaw π.seedLaw) :=
  (π.integrable_scalarPayoff w c).mul_bdd (measurable_individualScore i hh).aestronglyMeasurable
    ((B.individualScore_bounded_ae π.seedLaw i hb).mono (fun _ hv => by simpa only [Real.norm_eq_abs] using hv))

lemma RandomizedCountablePolicy.individualLikelihoodPolicy_scalarObjective {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) {θ : ℝ} (hθ : |θ| ≤ 1/4) (w c : ℝ) :
    (π.individualLikelihoodPolicy i h hh hb hm θ).scalarObjective w c=
      π.scalarObjective w c+θ*π.scalarIndividualLikelihoodDerivative i w c h := by
  have hTerm : (B.individualLikelihoodPath i h hh hb hm θ).terminal=B.terminal := by
    rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ]
    rfl
  have hPayoff : (π.individualLikelihoodPolicy i h hh hb hm θ).scalarPayoff w c=π.scalarPayoff w c := by
    funext v
    exact π.changeInstance_scalarPayoff _ _ hTerm w c v
  rw [(π.individualLikelihoodPolicy i h hh hb hm θ).scalarObjective_eq_integral,hPayoff]
  change (∫ v : CompleteWorld π.Seed, π.scalarPayoff w c v
    ∂(B.individualLikelihoodPath i h hh hb hm θ).completeWorldLaw π.seedLaw)=_
  rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ,
    B.individualLikelihoodTilt_completeWorldLaw i h hh hb hm θ hθ π.seedLaw,
    ProphetSecretary.Probability.integral_tiltLaw_eq_add (measurable_individualScore i hh)
      (B.individualScore_bounded_ae π.seedLaw i hb) (π.integrable_scalarPayoff w c) hθ,
    ← π.scalarObjective_eq_integral]
  rfl

lemma RandomizedCountablePolicy.individualLikelihoodPolicy_expectedDuration {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    (π.individualLikelihoodPolicy i h hh hb hm θ).expectedDuration=
      π.expectedDuration+θ*(∫ v, π.rule.realizedDuration v*h (v.2.1 i) ∂B.completeWorldLaw π.seedLaw) := by
  change (∫ v, π.rule.realizedDuration v ∂(B.individualLikelihoodPath i h hh hb hm θ).completeWorldLaw π.seedLaw)=_
  rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ,
    B.individualLikelihoodTilt_completeWorldLaw i h hh hb hm θ hθ π.seedLaw]
  exact ProphetSecretary.Probability.integral_tiltLaw_eq_add (measurable_individualScore i hh)
    (B.individualScore_bounded_ae π.seedLaw i hb) π.integrable_duration hθ

end ProphetSecretary.Limiting
