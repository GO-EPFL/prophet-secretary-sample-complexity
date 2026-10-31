import ProphetSecretary.Limiting.ConfigurationMeasurability
import ProphetSecretary.Probability.ChronologicalPayloadArray

/-!
# Actual Poisson configurations with chronological conditional payloads

The Poisson count is analytical and is never a policy input. One independent
infinite auxiliary sequence is fixed before that count is realized. The
per-count chronological array pushforward proves the entire mixed law of old
marks and occurrence tags, including an empty configuration and zero rate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

abbrev PayloadConfiguration (T : Type*) := Σ N : ℕ, Fin N → ℝ × (ℝ × T)

def payloadConfigurationMk {T : Type*} (N : ℕ) (v : Fin N → ℝ × (ℝ × T)) : PayloadConfiguration T := ⟨N,v⟩

lemma measurable_payloadConfiguration_mk {T : Type*} [MeasurableSpace T] (N : ℕ) :
    Measurable (payloadConfigurationMk (T := T) N) := Measurable.of_le_map (iInf_le _ N)

noncomputable def rateConfigurationLaw (rate : ℝ≥0) (p : Measure ℝ) : Measure Configuration :=
  Measure.sum (fun N : ℕ => ENNReal.ofReal (poissonWeight rate N) •
    (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod p)).map (configurationMk N))

lemma rateConfigurationLaw_actual (μ : FiniteMeasure ℝ) :
    rateConfigurationLaw μ.mass (μ.normalize : Measure ℝ)=configurationLaw μ := rfl

noncomputable def payloadConfigurationLaw {T : Type*} [MeasurableSpace T]
    (rate : ℝ≥0) (p : Measure ℝ) (κ : Measure T) : Measure (PayloadConfiguration T) :=
  Measure.sum (fun N : ℕ => ENNReal.ofReal (poissonWeight rate N) •
    (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ))).map (payloadConfigurationMk N))

lemma rateConfigurationLaw_count_map (rate : ℝ≥0) (p : Measure ℝ) [IsProbabilityMeasure p] :
    (rateConfigurationLaw rate p).map (fun ω : Configuration => ω.1)=poissonMeasure rate := by
  have hFiber (N : ℕ) : ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod p)).map (configurationMk N)).map
      (fun ω : Configuration => ω.1)=Measure.dirac N := by
    rw [Measure.map_map measurable_configuration_count (measurable_configuration_mk N)]
    change (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod p)).map (fun _ => N)=Measure.dirac N
    simp only [Measure.map_const,measure_univ,one_smul]
  rw [rateConfigurationLaw,Measure.map_sum measurable_configuration_count.aemeasurable]
  simp_rw [Measure.map_smul,hFiber]
  rfl

instance rateConfigurationLaw_probability (rate : ℝ≥0) (p : Measure ℝ) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (rateConfigurationLaw rate p) := by
  constructor
  have h := congrArg (fun m : Measure ℕ => m univ) (rateConfigurationLaw_count_map rate p)
  simpa only [Measure.map_apply measurable_configuration_count MeasurableSet.univ,Set.preimage_univ,measure_univ] using h

lemma measurable_payloadConfiguration_count {T : Type*} [MeasurableSpace T] :
    Measurable (fun ω : PayloadConfiguration T => ω.1) := by
  intro S hS
  change MeasurableSet[⨅ N : ℕ, (inferInstance : MeasurableSpace (Fin N → ℝ × (ℝ × T))).map (payloadConfigurationMk N)]
    ((fun ω : PayloadConfiguration T => ω.1) ⁻¹' S)
  rw [MeasurableSpace.measurableSet_iInf]
  intro N
  change MeasurableSet ((fun _ : Fin N → ℝ × (ℝ × T) => N) ⁻¹' S)
  exact measurable_const hS

lemma payloadConfigurationLaw_count_map {T : Type*} [MeasurableSpace T]
    (rate : ℝ≥0) (p : Measure ℝ) [IsProbabilityMeasure p] (κ : Measure T) [IsProbabilityMeasure κ] :
    (payloadConfigurationLaw rate p κ).map (fun ω : PayloadConfiguration T => ω.1)=poissonMeasure rate := by
  have hFiber (N : ℕ) : ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ))).map (payloadConfigurationMk N)).map
      (fun ω : PayloadConfiguration T => ω.1)=Measure.dirac N := by
    rw [Measure.map_map measurable_payloadConfiguration_count (measurable_payloadConfiguration_mk N)]
    change (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ))).map (fun _ => N)=Measure.dirac N
    simp only [Measure.map_const,measure_univ,one_smul]
  rw [payloadConfigurationLaw,Measure.map_sum measurable_payloadConfiguration_count.aemeasurable]
  simp_rw [Measure.map_smul,hFiber]
  rfl

instance payloadConfigurationLaw_probability {T : Type*} [MeasurableSpace T]
    (rate : ℝ≥0) (p : Measure ℝ) [IsProbabilityMeasure p] (κ : Measure T) [IsProbabilityMeasure κ] :
    IsProbabilityMeasure (payloadConfigurationLaw rate p κ) := by
  constructor
  have h := congrArg (fun m : Measure ℕ => m univ) (payloadConfigurationLaw_count_map rate p κ)
  simpa only [Measure.map_apply measurable_payloadConfiguration_count MeasurableSet.univ,Set.preimage_univ,measure_univ] using h

noncomputable def chronologicalPayloadConfiguration {U T : Type*} (F : ℝ × U → ℝ × T)
    (z : Configuration × (ℕ → U)) : PayloadConfiguration T :=
  ⟨z.1.1,fun i => ((z.1.2 i).1,F ((z.1.2 i).2,z.2 (Model.Instance.arrivalRank (fun j => (z.1.2 j).1) i).val))⟩

lemma measurable_chronologicalPayloadConfiguration {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (q p : Measure ℝ) [IsProbabilityMeasure q] [IsProbabilityMeasure p]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (κ : Measure T) [IsProbabilityMeasure κ]
    {F : ℝ × U → ℝ × T} (hF : MeasurePreserving F (q.prod ρ) (p.prod κ)) :
    Measurable (chronologicalPayloadConfiguration F) := by
  apply measurable_of_configuration_prod_branches
  intro N
  exact (measurable_payloadConfiguration_mk N).comp
    (ProphetSecretary.Probability.chronological_point_payload_array_measurePreserving (N := N) q p ρ κ hF).measurable

lemma chronologicalPayloadConfiguration_fiber_map {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (q p : Measure ℝ) [IsProbabilityMeasure q] [IsProbabilityMeasure p]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (κ : Measure T) [IsProbabilityMeasure κ]
    {F : ℝ × U → ℝ × T} (hF : MeasurePreserving F (q.prod ρ) (p.prod κ)) (N : ℕ) :
    (((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod q)).map (configurationMk N)).prod
      (Measure.infinitePi (fun _ : ℕ => ρ))).map (chronologicalPayloadConfiguration F)=
      (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ))).map (payloadConfigurationMk N) := by
  have hMap := measurable_chronologicalPayloadConfiguration q p ρ κ hF
  have hIn : MeasurePreserving (configurationMk N)
      (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod q))
      ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod q)).map (configurationMk N)) :=
    ⟨measurable_configuration_mk N,rfl⟩
  have hProduct := hIn.prod (MeasurePreserving.id (Measure.infinitePi (fun _ : ℕ => ρ)))
  rw [← hProduct.map_eq,Measure.map_map hMap hProduct.measurable]
  have hKernel := ProphetSecretary.Probability.chronological_point_payload_array_measurePreserving (N := N) q p ρ κ hF
  have hOut : MeasurePreserving (payloadConfigurationMk (T := T) N)
      (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ)))
      ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ))).map (payloadConfigurationMk N)) :=
    ⟨measurable_payloadConfiguration_mk N,rfl⟩
  exact (hOut.comp hKernel).map_eq

theorem chronologicalPayloadConfiguration_measurePreserving {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (rate : ℝ≥0) (q p : Measure ℝ) [IsProbabilityMeasure q] [IsProbabilityMeasure p]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (κ : Measure T) [IsProbabilityMeasure κ]
    {F : ℝ × U → ℝ × T} (hF : MeasurePreserving F (q.prod ρ) (p.prod κ)) :
    MeasurePreserving (chronologicalPayloadConfiguration F)
      ((rateConfigurationLaw rate q).prod (Measure.infinitePi (fun _ : ℕ => ρ)))
      (payloadConfigurationLaw rate p κ) := by
  have hMap := measurable_chronologicalPayloadConfiguration q p ρ κ hF
  refine ⟨hMap,?_⟩
  rw [rateConfigurationLaw,Measure.prod_sum_left,Measure.map_sum hMap.aemeasurable]
  simp_rw [Measure.prod_smul_left,Measure.map_smul,chronologicalPayloadConfiguration_fiber_map q p ρ κ hF]
  rfl

end ProphetSecretary.Limiting
