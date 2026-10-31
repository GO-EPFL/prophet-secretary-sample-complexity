import ProphetSecretary.Limiting.ChronologicalPoissonPayload

/-!
# Pointwise conditional-payload identities on the actual Poisson experiment

Every chronological mark/auxiliary pair has its independent product law.
A one-point almost-sure conditional identity therefore holds simultaneously
at every actual point of the finite Poisson configuration, including points
after stopping. This is an analytical identity, not information for a policy.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

lemma chronological_pairs_ae_mem {U : Type*} [MeasurableSpace U]
    (rate : ℝ≥0) (q : Measure ℝ) [IsProbabilityMeasure q] (ρ : Measure U) [IsProbabilityMeasure ρ]
    {G : Set (ℝ × U)} (hG : MeasurableSet G) (hGood : ∀ᵐ z ∂q.prod ρ, z∈G) :
    ∀ᵐ z : Configuration × (ℕ → U) ∂(rateConfigurationLaw rate q).prod (Measure.infinitePi (fun _ : ℕ => ρ)),
      ∀ j : Fin z.1.1, ((z.1.2 j).2,z.2 (Model.Instance.arrivalRank (fun k : Fin z.1.1 => (z.1.2 k).1) j).val)∈G := by
  let P := fun ω : PayloadConfiguration U => ∀ j : Fin ω.1, (ω.2 j).2∈G
  have hP : MeasurableSet {ω : PayloadConfiguration U | P ω} := by
    change MeasurableSet[⨅ N : ℕ, (inferInstance : MeasurableSpace (Fin N → ℝ × (ℝ × U))).map (payloadConfigurationMk N)] {ω | P ω}
    rw [MeasurableSpace.measurableSet_iInf]
    intro N
    change MeasurableSet {v : Fin N → ℝ × (ℝ × U) | ∀ j, (v j).2∈G}
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun j => hG.preimage (measurable_pi_apply j).snd)
  have hTarget : ∀ᵐ ω : PayloadConfiguration U ∂payloadConfigurationLaw rate q ρ, P ω := by
    rw [payloadConfigurationLaw,Measure.ae_sum_iff]
    intro N
    have hArray : ∀ᵐ v ∂Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (q.prod ρ)),
        ∀ j, (v j).2∈G := by
      apply ae_all_iff.mpr
      intro j
      have hEval : MeasurePreserving (fun v : Fin N → ℝ × (ℝ × U) => v j)
          (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (q.prod ρ)))
          (Model.Instance.uniformClock.prod (q.prod ρ)) := measurePreserving_eval _ j
      have hPair := (measurePreserving_snd : MeasurePreserving (Prod.snd : ℝ × (ℝ × U) → ℝ × U)
        (Model.Instance.uniformClock.prod (q.prod ρ)) (q.prod ρ)).comp hEval
      exact hPair.quasiMeasurePreserving.ae hGood
    have hFiber : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (q.prod ρ))).map (payloadConfigurationMk N), P ω :=
      (ae_map_iff (measurable_payloadConfiguration_mk N).aemeasurable hP).mpr hArray
    exact Measure.ae_smul_measure hFiber _
  have hMap := chronologicalPayloadConfiguration_measurePreserving rate q q ρ ρ (MeasurePreserving.id (q.prod ρ))
  exact hMap.quasiMeasurePreserving.ae hTarget

lemma chronological_payload_graph_ae {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (rate : ℝ≥0) (q : Measure ℝ) [IsProbabilityMeasure q] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ × T) (hF : Measurable F) (g : ℝ × T → ℝ) (hg : Measurable g)
    (hGraph : ∀ᵐ z ∂q.prod ρ, g (F z)=z.1) :
    ∀ᵐ z : Configuration × (ℕ → U) ∂(rateConfigurationLaw rate q).prod (Measure.infinitePi (fun _ : ℕ => ρ)),
      ∀ j : Fin z.1.1,
        g (F ((z.1.2 j).2,z.2 (Model.Instance.arrivalRank (fun k : Fin z.1.1 => (z.1.2 k).1) j).val))=(z.1.2 j).2 :=
  chronological_pairs_ae_mem rate q ρ (measurableSet_eq_fun (hg.comp hF) measurable_fst) hGraph

end ProphetSecretary.Limiting
