import ProphetSecretary.Limiting.CountableBandObservations
import ProphetSecretary.Limiting.ConfigurationStandardBorel
import ProphetSecretary.Probability.ObservationCoupling

/-!
# An actual coupling for causal omission of low Poisson observations

The original configuration and the independently sampled high/low pieces have
exact marginals. Countable band observations recover equality of their full
counting measures almost surely. The coupling is analytical; its extra old
configuration and future points are not supplied to a policy.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

abbrev SplitCloud := Configuration × Measure Point

noncomputable def splitCloudLaw (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) : Measure SplitCloud :=
  (configurationLaw (B.intensityAbove b hb)).prod (B.lowCloudLaw b)

instance splitCloudLaw_probability (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    IsProbabilityMeasure (B.splitCloudLaw hb) := by unfold splitCloudLaw; infer_instance

noncomputable def joinedCloud (q : SplitCloud) : Measure Point := countingMeasure q.1 + q.2

lemma measurable_joinedCloud : Measurable joinedCloud :=
  (measurable_countingMeasure.comp measurable_fst).add measurable_snd

lemma joinedCloud_measurePreserving (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    MeasurePreserving joinedCloud (B.splitCloudLaw hb) (B.bandConfigurationsLaw.map bandCountingMeasure) := by
  have hpair : MeasurePreserving (fun q : SplitCloud => (countingMeasure q.1,q.2)) (B.splitCloudLaw hb)
      (((configurationLaw (B.intensityAbove b hb)).map countingMeasure).prod (B.lowCloudLaw b)) :=
    (⟨measurable_countingMeasure,rfl⟩ : MeasurePreserving countingMeasure
      (configurationLaw (B.intensityAbove b hb)) ((configurationLaw (B.intensityAbove b hb)).map countingMeasure)).prod
      (MeasurePreserving.id (B.lowCloudLaw b))
  refine ⟨measurable_joinedCloud,?_⟩
  have he := (⟨measurable_fst.add measurable_snd,rfl⟩ : MeasurePreserving
    (fun q : Measure Point × Measure Point => q.1+q.2)
    (((configurationLaw (B.intensityAbove b hb)).map countingMeasure).prod (B.lowCloudLaw b))
    ((((configurationLaw (B.intensityAbove b hb)).map countingMeasure).prod (B.lowCloudLaw b)).map
      (fun q : Measure Point × Measure Point => q.1+q.2))).comp hpair
  exact he.map_eq.trans (B.bandCountingMeasure_poisson_low_law hb).symm

lemma exists_omissionCloud_coupling (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∃ γ : Measure (SplitCloud × BandConfigurations), IsProbabilityMeasure γ ∧
      MeasurePreserving Prod.fst γ (B.splitCloudLaw hb) ∧
      MeasurePreserving Prod.snd γ B.bandConfigurationsLaw ∧
      (∀ᵐ q ∂γ, bandCountingMeasure q.2 = joinedCloud q.1) := by
  let ρ := B.bandConfigurationsLaw.map bandCountingMeasure
  let X : BandConfigurations → BandObservations := fun ω => bandObservations B (bandCountingMeasure ω)
  let Z : SplitCloud → BandObservations := fun q => bandObservations B (joinedCloud q)
  have hX : Measurable X := (B.measurable_bandObservations).comp measurable_bandCountingMeasure
  have hZ : Measurable Z := (B.measurable_bandObservations).comp measurable_joinedCloud
  have hObsMP : MeasurePreserving (bandObservations B) ρ (ρ.map (bandObservations B)) :=
    ⟨B.measurable_bandObservations,rfl⟩
  have hOldObs : MeasurePreserving X B.bandConfigurationsLaw (ρ.map (bandObservations B)) :=
    hObsMP.comp (⟨measurable_bandCountingMeasure,rfl⟩ : MeasurePreserving
      bandCountingMeasure B.bandConfigurationsLaw ρ)
  have hNewObs : MeasurePreserving Z (B.splitCloudLaw hb) (ρ.map (bandObservations B)) :=
    hObsMP.comp (B.joinedCloud_measurePreserving hb)
  have hLaw : B.bandConfigurationsLaw.map X = (B.splitCloudLaw hb).map Z :=
    hOldObs.map_eq.trans hNewObs.map_eq.symm
  have hGraph : MeasurableSet {q : BandObservations × BandConfigurations | X q.2 = q.1} :=
    measurableSet_eq_fun (hX.comp measurable_snd) measurable_fst
  obtain ⟨γ,hγ,hNew,hOld,hShared⟩ := ProphetSecretary.Probability.exists_common_observation_coupling
    B.bandConfigurationsLaw (B.splitCloudLaw hb) hX hZ hLaw hGraph
  have hRegular : ∀ᵐ μ ∂ρ, RegularBandMeasure B μ :=
    (ae_map_iff measurable_bandCountingMeasure.aemeasurable B.measurableSet_regularBandMeasure).mpr B.bandCountingMeasure_regular_ae
  have hNewRegular : ∀ᵐ q ∂B.splitCloudLaw hb, RegularBandMeasure B (joinedCloud q) :=
    (B.joinedCloud_measurePreserving hb).quasiMeasurePreserving.ae hRegular
  refine ⟨γ,hγ,hNew,hOld,?_⟩
  filter_upwards [hShared,hOld.quasiMeasurePreserving.ae B.bandCountingMeasure_regular_ae,
    hNew.quasiMeasurePreserving.ae hNewRegular] with q hq ho hn
  exact B.eq_of_bandObservations _ _ ho hn hq

end ProphetSecretary.Limiting.CountableInstance
