import ProphetSecretary.Limiting.PoissonPayloadIntensity
import ProphetSecretary.Limiting.ChronologicalPayloadGraph
import ProphetSecretary.Limiting.HybridPolicy

/-!
# The conditional display graph on every actual hybrid offer

Projection of the complete hybrid product law retains the true configuration
and independent chronological auxiliary sequence. The one-point conditional
graph therefore holds at every anonymous occurrence, for arbitrary independent
retained offers and policy randomness.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

lemma hybrid_chronological_payload_graph_ae {n : ℕ} {Seed U T : Type*}
    [MeasurableSpace Seed] [MeasurableSpace U] [MeasurableSpace T]
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (κ : Measure T) [IsProbabilityMeasure κ]
    (F : ℝ × U → ℝ × T) (hF : Measurable F) (g : ℝ × T → ℝ) (hg : Measurable g)
    (hGraph : ∀ᵐ z ∂(displayedPayloadMarkLaw μ κ g hg : Measure ℝ).prod ρ, g (F z)=z.1) :
    ∀ᵐ v : HybridWorld n (Seed × (ℕ → U)) ∂hybridWorldLaw P (displayedPayloadIntensity μ κ g hg)
      (ν.prod (Measure.infinitePi (fun _ : ℕ => ρ))), ∀ j : Fin v.1.1,
      g (F ((v.1.2 j).2,v.2.2.2.2 (Model.Instance.arrivalRank (fun k : Fin v.1.1 => (v.1.2 k).1) j).val))=(v.1.2 j).2 := by
  let K := Measure.infinitePi (fun _ : ℕ => ρ)
  have hAux : MeasurePreserving (fun z : Model.World n (Seed × (ℕ → U)) => z.2.2.2)
      (P.worldLaw (ν.prod K)) K := measurePreserving_snd.comp (measurePreserving_snd.comp measurePreserving_snd)
  have hPair := (MeasurePreserving.id (configurationLaw (displayedPayloadIntensity μ κ g hg))).prod hAux
  have hRate : MeasurePreserving (fun v : HybridWorld n (Seed × (ℕ → U)) => (v.1,v.2.2.2.2))
      (hybridWorldLaw P (displayedPayloadIntensity μ κ g hg) (ν.prod K))
      ((rateConfigurationLaw μ.mass (displayedPayloadMarkLaw μ κ g hg : Measure ℝ)).prod K) := by
    refine ⟨hPair.measurable,hPair.map_eq.trans ?_⟩
    rw [configurationLaw_displayedPayloadIntensity]
  exact hRate.quasiMeasurePreserving.ae
    (chronological_payload_graph_ae μ.mass (displayedPayloadMarkLaw μ κ g hg : Measure ℝ) ρ F hF g hg hGraph)

end ProphetSecretary.Limiting
