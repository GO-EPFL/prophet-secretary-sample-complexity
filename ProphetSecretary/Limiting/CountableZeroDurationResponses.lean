import ProphetSecretary.Limiting.CountableSelectionValueConstancy
import ProphetSecretary.Limiting.CountableIndividualResponses

/-!
# The individual zero-duration-response alternative

The likelihood path changes a single marginal while keeping the canonical
base policy fixed. Its proved derivative identity turns vanishing duration
responses into the covariance hypothesis, hence into actual duration and
selected-occurrence constancy throughout the supported convex hull.
This is the first individual-variable step of `lem:nonzero`.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

theorem canonical_zero_duration_scores_of_zero_responses (B : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hResponse : ∀ (φ : ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, |φ x| ≤ 1)
      (hMean : (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0),
      HasDerivAt (fun θ => ((B.valuePolicy hw hc).individualLikelihoodPolicy i φ hm
        (Eventually.of_forall hb) hMean θ).expectedDuration) 0 0) :
    ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0 := by
  intro φ hm hb hMean
  have hDerivative := (B.valuePolicy hw hc).hasDerivAt_expectedDuration_individualLikelihoodPolicy
    i φ hm (Eventually.of_forall hb) hMean
  have hEq := hDerivative.unique (hResponse φ hm hb hMean)
  change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*φ (v.2.1 i)
    ∂B.completeWorldLaw (Measure.dirac ()))=0 at hEq
  simpa only [mul_comm] using hEq

theorem canonical_duration_and_selection_constant_of_zero_responses
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hResponse : ∀ (φ : ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, |φ x| ≤ 1)
      (hMean : (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0),
      HasDerivAt (fun θ => ((B.valuePolicy hw hc).individualLikelihoodPolicy i φ hm
        (Eventually.of_forall hb) hMean θ).expectedDuration) 0 0) :
    ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ x ∈ convexHull ℝ (B.individuals i : Measure ℝ).support,
        (B.valueRule w c).durationAtValue i (v,x)=(B.valueRule w c).realizedDuration v ∧
        FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime (replaceIndividualValue i (v,x))=
          FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime v := by
  have hScores := B.canonical_zero_duration_scores_of_zero_responses hw hc i hResponse
  filter_upwards [B.canonical_durationAtValue_ae_constant_on_support_hull hZero hw hc i hScores,
    B.canonical_selectedCodeAtValue_ae_constant_on_support_hull hZero hw hc i hScores]
    with v hDuration hSelection x hx
  exact ⟨hDuration x hx,hSelection x hx⟩

end ProphetSecretary.Limiting.CountableInstance
