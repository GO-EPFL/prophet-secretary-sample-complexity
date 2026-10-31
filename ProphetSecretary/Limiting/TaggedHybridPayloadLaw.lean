import ProphetSecretary.Limiting.TaggedHybridPayloadEvaluation
import ProphetSecretary.Limiting.Support
import ProphetSecretary.Model.ClockReplacement

/-!
# The actual observation law of a tagged hybrid policy

The retained values and clocks, count-hidden anonymous process, independent
policy seed and chronological tags retain their exact product laws. Payload
evaluation agrees almost surely with the ordinary hybrid policy, so its
expected reward and duration are identified without an optimizer assumption.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

noncomputable def taggedHybridWorldLaw {n : ℕ} {Seed T : Type*} [MeasurableSpace Seed] [MeasurableSpace T]
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) (κ : Measure T) :
    Measure (PayloadConfiguration T × Model.World n Seed) :=
  (payloadConfigurationLaw B.intensity.mass (B.intensity.normalize : Measure ℝ) κ).prod (B.individuals.worldLaw ν)

noncomputable def sampledTaggedHybridWorld {n : ℕ} {Seed T : Type*}
    (v : HybridWorld n (Seed × (ℕ → T))) : PayloadConfiguration T × Model.World n Seed :=
  (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (v.1,v.2.2.2.2),(v.2.1,(v.2.2.1,v.2.2.2.1)))

lemma sampledTaggedHybridWorld_measurePreserving {n : ℕ} {Seed T : Type*}
    [MeasurableSpace Seed] [MeasurableSpace T] (B : FiniteIntensityHybridInstance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (κ : Measure T) [IsProbabilityMeasure κ] :
    MeasurePreserving sampledTaggedHybridWorld (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ))))
      (taggedHybridWorldLaw B ν κ) := by
  let K := Measure.infinitePi (fun _ : ℕ => κ)
  let P := B.individuals
  have hOne := (MeasurePreserving.id P.valuesLaw).prod
    ((measurePreserving_prodAssoc (Model.Instance.clocksLaw n) ν K).symm MeasurableEquiv.prodAssoc)
  have hTwo := (measurePreserving_prodAssoc P.valuesLaw ((Model.Instance.clocksLaw n).prod ν) K).symm MeasurableEquiv.prodAssoc
  have hOuter := (MeasurePreserving.id (configurationLaw B.intensity)).prod (hTwo.comp hOne)
  have hAssoc := (measurePreserving_prodAssoc (configurationLaw B.intensity) (P.worldLaw ν) K).symm MeasurableEquiv.prodAssoc
  have hSwap := Model.measurePreserving_swap_last (configurationLaw B.intensity) (P.worldLaw ν) K
  have hPayload := chronologicalPayloadConfiguration_measurePreserving B.intensity.mass
    (B.intensity.normalize : Measure ℝ) (B.intensity.normalize : Measure ℝ) κ κ
    (MeasurePreserving.id ((B.intensity.normalize : Measure ℝ).prod κ))
  change MeasurePreserving (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T))
    ((configurationLaw B.intensity).prod K) (payloadConfigurationLaw B.intensity.mass (B.intensity.normalize : Measure ℝ) κ) at hPayload
  exact (hPayload.prod (MeasurePreserving.id (P.worldLaw ν))).comp (hSwap.comp (hAssoc.comp hOuter))

lemma TaggedHybridRule.integral_payloadReward_eq {n : ℕ} {Seed T : Type*}
    [MeasurableSpace Seed] [MeasurableSpace T] (π : TaggedHybridRule n Seed T) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) :
    (∫ v, π.payloadReward t0 v ∂taggedHybridWorldLaw B ν κ)=
      ∫ v, π.sampleTags.realizedReward 0 v ∂B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ))) := by
  have hMP := sampledTaggedHybridWorld_measurePreserving B ν κ
  have hMean := hMP.hasLaw.integral_comp (π.measurable_payloadReward hπ t0).aestronglyMeasurable
  have hCfg : MeasurePreserving (Prod.fst : HybridWorld n (Seed × (ℕ → T)) → Configuration)
      (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ)))) (configurationLaw B.intensity) := measurePreserving_fst
  have hAE := hCfg.quasiMeasurePreserving.ae (configuration_times_distinct B.intensity)
  rw [← hMean]
  apply integral_congr_ae
  filter_upwards [hAE] with v hv
  exact (π.payload_outcomes_assigned t0 v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 hv).1

lemma TaggedHybridRule.integral_payloadDuration_eq {n : ℕ} {Seed T : Type*}
    [MeasurableSpace Seed] [MeasurableSpace T] (π : TaggedHybridRule n Seed T) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) :
    (∫ v, π.payloadDuration t0 v ∂taggedHybridWorldLaw B ν κ)=
      ∫ v, π.sampleTags.realizedDuration v ∂B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ))) := by
  have hMP := sampledTaggedHybridWorld_measurePreserving B ν κ
  have hMean := hMP.hasLaw.integral_comp (π.measurable_payloadDuration hπ t0).aestronglyMeasurable
  have hCfg : MeasurePreserving (Prod.fst : HybridWorld n (Seed × (ℕ → T)) → Configuration)
      (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ)))) (configurationLaw B.intensity) := measurePreserving_fst
  have hAE := hCfg.quasiMeasurePreserving.ae (configuration_times_distinct B.intensity)
  rw [← hMean]
  apply integral_congr_ae
  filter_upwards [hAE] with v hv
  exact (π.payload_outcomes_assigned t0 v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 hv).2

end ProphetSecretary.Limiting
