import ProphetSecretary.Limiting.CountableConditionalIndividualWorld
import ProphetSecretary.Limiting.CountableSeededIndividualPullback
import ProphetSecretary.Limiting.CountableSeedTransport

/-!
# Causal policies using conditionally reconstructed individual values

An old value is reconstructed only from the current displayed value and one
independent auxiliary draw. Its already observed history entry uses the same
draw. The full world pushforward proves admissibility and duration transport.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedCountablePolicy
variable {B : CountableInstance}

noncomputable def reconstructIndividualPolicy (π : RandomizedCountablePolicy B) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ)) :
    RandomizedCountablePolicy (B.updateIndividual i q hSupport) where
  Seed := π.Seed × U
  seedLaw := π.seedLaw.prod ρ
  rule := (π.rule.comapSeed Prod.fst).pullbackSeededIndividual i (fun r y => F (y,r.2))
  measurable_rule := (π.rule.comapSeed Prod.fst).pullbackSeededIndividual_isMeasurable
    (π.rule.comapSeed_isMeasurable π.measurable_rule measurable_fst) i
    (hF.measurable.comp (measurable_snd.prodMk measurable_fst.snd))
  admissible := by
    have hMP := B.recoverIndividualWorld_measurePreserving i q hSupport π.seedLaw ρ hF
    filter_upwards [hMP.quasiMeasurePreserving.ae π.admissible] with v hv
    apply ((π.rule.comapSeed Prod.fst).pullbackSeededIndividual_hasFirst i (fun r y => F (y,r.2)) v).mpr
    exact hv

lemma reconstructIndividualPolicy_duration (π : RandomizedCountablePolicy B) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ))
    (v : CompleteWorld (π.Seed × U)) :
    (π.reconstructIndividualPolicy i q hSupport ρ F hF).rule.realizedDuration v=
      π.rule.realizedDuration (recoverIndividualWorld i F v) := by
  exact (π.rule.comapSeed Prod.fst).pullbackSeededIndividual_duration i (fun r y => F (y,r.2)) v

lemma reconstructIndividualPolicy_expectedDuration (π : RandomizedCountablePolicy B) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ)) :
    (π.reconstructIndividualPolicy i q hSupport ρ F hF).expectedDuration=π.expectedDuration := by
  have hMP := B.recoverIndividualWorld_measurePreserving i q hSupport π.seedLaw ρ hF
  have hMean := hMP.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  change (∫ v, (π.reconstructIndividualPolicy i q hSupport ρ F hF).rule.realizedDuration v
    ∂(B.updateIndividual i q hSupport).completeWorldLaw (π.seedLaw.prod ρ))=
      ∫ v, π.rule.realizedDuration v ∂B.completeWorldLaw π.seedLaw
  rw [← hMean]
  exact integral_congr_ae (Eventually.of_forall (π.reconstructIndividualPolicy_duration i q hSupport ρ F hF))

lemma reconstructIndividualPolicy_selection (π : RandomizedCountablePolicy B) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ))
    (v : CompleteWorld (π.Seed × U)) :
    (π.reconstructIndividualPolicy i q hSupport ρ F hF).rule.individualSelectionIndicator i v=
      π.rule.individualSelectionIndicator i (recoverIndividualWorld i F v) := by
  simp only [CountableRule.individualSelectionIndicator_eq_code]
  change (if FirstAcceptance.selectedCode ((π.rule.comapSeed Prod.fst).pullbackSeededIndividual i (fun r y => F (y,r.2))).codeAccepted codeTime v=_ then _ else _)=_
  rw [CountableRule.pullbackSeededIndividual_selectedCode]
  rfl

end RandomizedCountablePolicy
end ProphetSecretary.Limiting
