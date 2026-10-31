import ProphetSecretary.Limiting.TruncatedObserverActions
import ProphetSecretary.Limiting.CountableCutoffLaw
import ProphetSecretary.Probability.FiniteMeasureTotalization

/-!
# The actual common finite-observer law

The complete high-mark measure is analytical input for a payoff functional;
callbacks receive only the corresponding strict past. Both the full countable
world and the finite hybrid world project to the same actual product law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def configurationFiniteMeasure (ω : Configuration) : FiniteMeasure Point :=
  ProphetSecretary.Probability.finiteMeasureOrZero (countingMeasure ω)

lemma measurable_configurationFiniteMeasure : Measurable configurationFiniteMeasure :=
  ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp measurable_countingMeasure

lemma configurationFiniteMeasure_coe (ω : Configuration) :
    (configurationFiniteMeasure ω : Measure Point) = countingMeasure ω := by
  apply ProphetSecretary.Probability.finiteMeasureOrZero_coe
  unfold countingMeasure
  infer_instance

noncomputable def finiteCutoffCountingMeasure (b : ℝ) (ω : BandConfigurations) : FiniteMeasure Point :=
  ProphetSecretary.Probability.finiteMeasureOrZero ((bandCountingMeasure ω).restrict (univ ×ˢ Ioi b))

lemma measurable_finiteCutoffCountingMeasure (b : ℝ) : Measurable (finiteCutoffCountingMeasure b) :=
  ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp (measurable_cutoffCountingMeasure b)

namespace CountableInstance

variable (B : CountableInstance)

lemma finiteCutoffCountingMeasure_coe_ae {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, (finiteCutoffCountingMeasure b ω : Measure Point) =
      (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b) := by
  filter_upwards [B.bandCountingMeasure_region_finite_ae hb
    (MeasurableSet.univ.prod measurableSet_Ioi) (fun _ h => h)] with ω hω
  apply ProphetSecretary.Probability.finiteMeasureOrZero_coe
  constructor
  simpa only [Measure.restrict_apply_univ] using hω

lemma finiteCutoffCountingMeasure_law {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    B.bandConfigurationsLaw.map (finiteCutoffCountingMeasure b) =
      (configurationLaw (B.intensityAbove b hb)).map configurationFiniteMeasure := by
  have hl := congrArg (fun M : Measure (Measure Point) =>
    M.map (ProphetSecretary.Probability.finiteMeasureOrZero (α := Point))) (B.cutoff_countingMeasure_law hb)
  rw [Measure.map_map ProphetSecretary.Probability.measurable_finiteMeasureOrZero
    (measurable_cutoffCountingMeasure b),
    Measure.map_map ProphetSecretary.Probability.measurable_finiteMeasureOrZero measurable_countingMeasure] at hl
  exact hl

end CountableInstance

noncomputable def finiteObserverLaw {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) : Measure (FiniteObserverWorld n Seed) :=
  ((configurationLaw μ).map configurationFiniteMeasure).prod (P.worldLaw ν)

instance finiteObserverLaw_probability {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finiteObserverLaw P μ ν) := by
  unfold finiteObserverLaw
  haveI : IsProbabilityMeasure ((configurationLaw μ).map configurationFiniteMeasure) :=
    Measure.isProbabilityMeasure_map measurable_configurationFiniteMeasure.aemeasurable
  infer_instance

lemma hybrid_finiteObserver_measurePreserving {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : HybridWorld n Seed => (configurationFiniteMeasure v.1,v.2))
      (hybridWorldLaw P μ ν) (finiteObserverLaw P μ ν) :=
  (⟨measurable_configurationFiniteMeasure,rfl⟩ :
    MeasurePreserving configurationFiniteMeasure (configurationLaw μ)
      ((configurationLaw μ).map configurationFiniteMeasure)).prod (MeasurePreserving.id (P.worldLaw ν))

namespace CountableInstance

lemma finiteObserverProjection_measurePreserving (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    MeasurePreserving (fun v : CompleteWorld Seed => truncatedObserverWorld (N := N) (finiteCutoffCountingMeasure b v.1) v)
      (B.completeWorldLaw ν) (finiteObserverLaw (B.individualPrefix N) (B.intensityAbove b hb) ν) :=
  (⟨measurable_finiteCutoffCountingMeasure b,B.finiteCutoffCountingMeasure_law hb⟩ :
    MeasurePreserving (finiteCutoffCountingMeasure b) B.bandConfigurationsLaw
      ((configurationLaw (B.intensityAbove b hb)).map configurationFiniteMeasure)).prod
      (B.prefixWorld_measurePreserving ν N)

end CountableInstance
end ProphetSecretary.Limiting
