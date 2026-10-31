import ProphetSecretary.Limiting.CountableIndividualTaggedPolicies
import ProphetSecretary.Limiting.CountableIndividualPayloadOutcomes

/-!
# Observable inverse simulation for an occurrence-tagged individual

Joint conditional payload sampling preserves the old value and independent tag
law. Exact causal execution, rather than an early disclosure of the tag,
transports admissibility, selection and duration to the displayed instance.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

noncomputable def reconstructPolicy (π : RandomizedIndividualTaggedPolicy B i κ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ × T) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) ((B.individuals i : Measure ℝ).prod κ))
    (t0 : T) : RandomizedCountablePolicy (B.updateIndividual i q hSupport) where
  Seed := π.Seed × U
  seedLaw := π.seedLaw.prod ρ
  rule := π.rule.pullbackIndividualPayload i F t0
  measurable_rule := π.rule.pullbackIndividualPayload_isMeasurable π.measurable_rule i hF.measurable t0
  admissible := by
    have hMP := B.recoverIndividualPayloadWorld_measurePreserving i q hSupport π.seedLaw ρ κ hF
    filter_upwards [hMP.quasiMeasurePreserving.ae π.admissible] with v hv
    exact (π.rule.pullbackIndividualPayload_hasFirst i F t0 π.blind_before v).mpr hv

lemma reconstructPolicy_expectedDuration (π : RandomizedIndividualTaggedPolicy B i κ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ × T) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) ((B.individuals i : Measure ℝ).prod κ))
    (t0 : T) : (π.reconstructPolicy q hSupport ρ F hF t0).expectedDuration=π.toBasePolicy.expectedDuration := by
  have hMP := B.recoverIndividualPayloadWorld_measurePreserving i q hSupport π.seedLaw ρ κ hF
  have hMean := hMP.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  change (∫ v : CompleteWorld (π.Seed × U), (π.rule.pullbackIndividualPayload i F t0).realizedDuration v
    ∂(B.updateIndividual i q hSupport).completeWorldLaw (π.seedLaw.prod ρ))=
      ∫ v, π.rule.realizedDuration v ∂B.completeWorldLaw (π.seedLaw.prod κ)
  rw [← hMean]
  exact integral_congr_ae (Eventually.of_forall (π.rule.pullbackIndividualPayload_duration i F t0 π.blind_before))

lemma reconstructPolicy_selection (π : RandomizedIndividualTaggedPolicy B i κ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ × T) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) ((B.individuals i : Measure ℝ).prod κ))
    (t0 : T) (v : CompleteWorld (π.Seed × U)) :
    (π.reconstructPolicy q hSupport ρ F hF t0).rule.individualSelectionIndicator i v=
      π.rule.individualSelectionIndicator i (recoverIndividualPayloadWorld i F v) := by
  simp only [CountableRule.individualSelectionIndicator_eq_code]
  change (if FirstAcceptance.selectedCode (π.rule.pullbackIndividualPayload i F t0).codeAccepted codeTime v=_ then _ else _)=_
  rw [CountableRule.pullbackIndividualPayload_selectedCode π.rule i F t0 π.blind_before]

end RandomizedIndividualTaggedPolicy
end ProphetSecretary.Limiting
