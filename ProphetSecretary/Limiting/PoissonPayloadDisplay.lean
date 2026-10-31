import ProphetSecretary.Limiting.PoissonPayloadIntensity
import ProphetSecretary.Limiting.TaggedHybridPayloadEvaluation
import ProphetSecretary.Probability.CountableMixtureMeasurability

/-!
# The actual forward display law of tagged Poisson configurations

The display map preserves clocks and acts independently on each actual mark
payload. Product pushforwards on every count fiber give the full displayed
Poisson law. The count is an analytical mixture index and is not observed by
any callback.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

def displayPayloadPoint (g : ℝ × T → ℝ) (p : ℝ × (ℝ × T)) : Point := (p.1,g p.2)

lemma measurable_displayPayloadPoint {g : ℝ × T → ℝ} (hg : Measurable g) : Measurable (displayPayloadPoint g) :=
  measurable_fst.prodMk (hg.comp measurable_snd)

noncomputable def displayPayloadConfiguration (g : ℝ × T → ℝ) (ω : PayloadConfiguration T) : Configuration :=
  ⟨ω.1,fun j => displayPayloadPoint g (ω.2 j)⟩

lemma measurable_displayPayloadConfiguration {g : ℝ × T → ℝ} (hg : Measurable g) :
    Measurable (displayPayloadConfiguration g) := by
  apply ProphetSecretary.Probability.measurable_of_sigma_branches
  intro N
  exact (measurable_configuration_mk N).comp
    (measurable_pi_lambda _ (fun j => (measurable_displayPayloadPoint hg).comp (measurable_pi_apply j)))

theorem displayPayloadConfiguration_measurePreserving (μ : FiniteMeasure ℝ)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g) :
    MeasurePreserving (displayPayloadConfiguration g)
      (payloadConfigurationLaw μ.mass (μ.normalize : Measure ℝ) κ)
      (configurationLaw (displayedPayloadIntensity μ κ g hg)) := by
  let q := displayedPayloadMarkLaw μ κ g hg
  have hMark : MeasurePreserving g ((μ.normalize : Measure ℝ).prod κ) (q : Measure ℝ) := ⟨hg,rfl⟩
  have hPoint := (MeasurePreserving.id Model.Instance.uniformClock).prod hMark
  have hMap := measurable_displayPayloadConfiguration hg
  have hFiber (N : ℕ) :
      ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod ((μ.normalize : Measure ℝ).prod κ))).map
        (payloadConfigurationMk N)).map (displayPayloadConfiguration g)=
      (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (q : Measure ℝ))).map (configurationMk N) := by
    rw [Measure.map_map hMap (measurable_payloadConfiguration_mk N)]
    have hRows := measurePreserving_pi
      (fun _ : Fin N => Model.Instance.uniformClock.prod ((μ.normalize : Measure ℝ).prod κ))
      (fun _ : Fin N => Model.Instance.uniformClock.prod (q : Measure ℝ)) (fun _ => hPoint)
    have hOut : MeasurePreserving (configurationMk N)
        (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (q : Measure ℝ)))
        ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (q : Measure ℝ))).map (configurationMk N)) :=
      ⟨measurable_configuration_mk N,rfl⟩
    exact (hOut.comp hRows).map_eq
  refine ⟨hMap,?_⟩
  rw [configurationLaw_displayedPayloadIntensity,payloadConfigurationLaw,Measure.map_sum hMap.aemeasurable]
  simp_rw [Measure.map_smul,hFiber]
  rfl

lemma displayedPayloadIntensity_fst (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ] :
    displayedPayloadIntensity μ κ (Prod.fst : ℝ × T → ℝ) measurable_fst=μ := by
  apply FiniteMeasure.toMeasure_injective
  rw [displayedPayloadIntensity_toMeasure]
  exact (measurePreserving_fst : MeasurePreserving (Prod.fst : ℝ × T → ℝ)
    ((μ : Measure ℝ).prod κ) (μ : Measure ℝ)).map_eq

lemma forgetPayloadConfiguration_measurePreserving (μ : FiniteMeasure ℝ)
    (κ : Measure T) [IsProbabilityMeasure κ] :
    MeasurePreserving (forgetPayloadConfiguration (T := T))
      (payloadConfigurationLaw μ.mass (μ.normalize : Measure ℝ) κ) (configurationLaw μ) := by
  have h := displayPayloadConfiguration_measurePreserving μ κ (Prod.fst : ℝ × T → ℝ) measurable_fst
  rw [displayedPayloadIntensity_fst] at h
  exact h

end ProphetSecretary.Limiting
