import ProphetSecretary.Limiting.CountableCapping
import ProphetSecretary.Limiting.CountableIndividualPullback
import ProphetSecretary.Limiting.CountableReach
import Mathlib.Probability.HasLaw

/-!
# Actual individual-cap policy transport when the anonymous tail vanishes

The anonymous intensity is unchanged because min(x,K)=x almost everywhere.
The actual infinite individual product is pushed forward coordinatewise.
The causal pullback rule maps only observed individual values. First-attainment
admissibility, duration, and reach are transported by the constructed law map.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

lemma intensity_cap_eq_of_tail_zero (B : CountableInstance) (K : ℝ≥0)
    (hTail : B.intensity (Ioi (K:ℝ))=0) : B.intensity.map (Model.capValue K)=B.intensity := by
  have hBound : ∀ᵐ x ∂B.intensity, x≤(K:ℝ) :=
    (measure_eq_zero_iff_ae_notMem.mp hTail).mono fun _ hx => le_of_not_gt hx
  have hEq : Model.capValue K=ᵐ[B.intensity] id := hBound.mono fun _ hx => min_eq_left hx
  rw [Measure.map_congr hEq,Measure.map_id]

lemma capAt_bandConfigurationsLaw_eq (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) (hTail : B.intensity (Ioi (K:ℝ))=0) :
    (B.capAt hZero K hK).bandConfigurationsLaw=B.bandConfigurationsLaw := by
  let Q := B.capAt hZero K hK
  have hIntensity := B.intensity_cap_eq_of_tail_zero K hTail
  have hBand (k : ℕ) : Q.bandIntensity k=B.bandIntensity k := by
    have hMarks : Q.markBand k=B.markBand k := by
      simp only [markBand,markCutoff,Q,capAt,hZero]
    apply FiniteMeasure.toMeasure_injective
    change (B.intensity.map (Model.capValue K)).restrict (Q.markBand k)=B.intensity.restrict (B.markBand k)
    rw [hIntensity,hMarks]
  change Measure.infinitePi (fun k => configurationLaw (Q.bandIntensity k))=Measure.infinitePi (fun k => configurationLaw (B.bandIntensity k))
  have hFun : (fun k => configurationLaw (Q.bandIntensity k))=(fun k => configurationLaw (B.bandIntensity k)) :=
    funext fun k => congrArg configurationLaw (hBand k)
  rw [hFun]

lemma capAt_individualValues_measurePreserving (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) :
    MeasurePreserving (fun x : ℕ → ℝ => Model.capValue K ∘ x) B.individualValuesLaw (B.capAt hZero K hK).individualValuesLaw := by
  refine ⟨measurable_pi_lambda _ (fun i => (Model.measurable_capValue K).comp (measurable_pi_apply i)),?_⟩
  change (Measure.infinitePi (fun i => (B.individuals i : Measure ℝ))).map (fun x i => Model.capValue K (x i))=
    Measure.infinitePi (fun i => ((B.capAt hZero K hK).individuals i : Measure ℝ))
  rw [Measure.infinitePi_map_pi (fun i => (B.individuals i : Measure ℝ)) (fun _ => Model.measurable_capValue K)]
  rfl

lemma capAt_completeWorld_measurePreserving (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) (hTail : B.intensity (Ioi (K:ℝ))=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (mapIndividualWorld (Model.capValue K)) (B.completeWorldLaw ν)
      ((B.capAt hZero K hK).completeWorldLaw ν) := by
  have hCloud : MeasurePreserving (id : BandConfigurations → BandConfigurations) B.bandConfigurationsLaw (B.capAt hZero K hK).bandConfigurationsLaw := by
    refine ⟨measurable_id,?_⟩
    rw [Measure.map_id,B.capAt_bandConfigurationsLaw_eq hZero K hK hTail]
  exact hCloud.prod ((B.capAt_individualValues_measurePreserving hZero K hK).prod
    (MeasurePreserving.id (individualClocksLaw.prod ν)))

end ProphetSecretary.Limiting.CountableInstance

namespace ProphetSecretary.Limiting.RandomizedCountablePolicy
open CountableInstance
variable {B : CountableInstance}

noncomputable def individualCapPullback (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (hTail : B.intensity (Ioi (K:ℝ))=0) (π : RandomizedCountablePolicy (B.capAt hZero K hK)) : RandomizedCountablePolicy B where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.pullbackIndividualValues (Model.capValue K)
  measurable_rule := π.rule.pullbackIndividualValues_isMeasurable π.measurable_rule (Model.measurable_capValue K)
  admissible := by
    have hMP := B.capAt_completeWorld_measurePreserving hZero K hK hTail π.seedLaw
    filter_upwards [hMP.quasiMeasurePreserving.ae π.admissible] with v hv
    exact (π.rule.pullbackIndividualValues_hasFirst (Model.capValue K) v).mpr hv

lemma individualCapPullback_expectedDuration (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (hTail : B.intensity (Ioi (K:ℝ))=0) (π : RandomizedCountablePolicy (B.capAt hZero K hK)) :
    (individualCapPullback hZero K hK hTail π).expectedDuration=π.expectedDuration := by
  have hMP := B.capAt_completeWorld_measurePreserving hZero K hK hTail π.seedLaw
  have hMap := hMP.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  change (∫ v, (π.rule.pullbackIndividualValues (Model.capValue K)).realizedDuration v ∂B.completeWorldLaw π.seedLaw)=
    ∫ v, π.rule.realizedDuration v ∂(B.capAt hZero K hK).completeWorldLaw π.seedLaw
  rw [←hMap]
  apply integral_congr_ae
  exact Eventually.of_forall (π.rule.pullbackIndividualValues_duration (Model.capValue K))

lemma individualCapPullback_individualReachProbability (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (hTail : B.intensity (Ioi (K:ℝ))=0) (π : RandomizedCountablePolicy (B.capAt hZero K hK)) (i : ℕ) :
    (individualCapPullback hZero K hK hTail π).individualReachProbability i=π.individualReachProbability i := by
  have hMP := B.capAt_completeWorld_measurePreserving hZero K hK hTail π.seedLaw
  let E : Set (CompleteWorld π.Seed) := {v | v.2.2.1 i≤π.rule.realizedDuration v}
  have hE : MeasurableSet E := measurableSet_le
    ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    (π.rule.measurable_realizedDuration π.measurable_rule)
  have hMap := map_measureReal_apply (μ:=B.completeWorldLaw π.seedLaw) hMP.measurable hE
  rw [hMP.map_eq] at hMap
  change (B.completeWorldLaw π.seedLaw).real {v | v.2.2.1 i≤(π.rule.pullbackIndividualValues (Model.capValue K)).realizedDuration v}=
    ((B.capAt hZero K hK).completeWorldLaw π.seedLaw).real E
  rw [hMap]
  congr 1
  ext v
  change (v.2.2.1 i≤(π.rule.pullbackIndividualValues (Model.capValue K)).realizedDuration v) ↔
    v.2.2.1 i≤π.rule.realizedDuration (mapIndividualWorld (Model.capValue K) v)
  rw [π.rule.pullbackIndividualValues_duration]

end ProphetSecretary.Limiting.RandomizedCountablePolicy
