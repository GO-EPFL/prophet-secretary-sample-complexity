import ProphetSecretary.Limiting.TaggedHybridPayloadEvaluation
import ProphetSecretary.Limiting.TaggedHybridReconstructionRule

/-!
# Exact causal actions under conditional Poisson payload reconstruction

The reconstructed old array and displayed array have identical clocks and
retained data. At every candidate their actions agree, because their tagged
strict pasts and current payloads agree. The count and construction indices
serve only to compare the analytical executions.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

lemma payloadObservedHistory_from_sequence {T : Type*} [MeasurableSpace T]
    (t0 : T) (ω : PayloadConfiguration T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (t : ℝ) :
    chronologicalTaggedHistory (payloadTagSequence t0 ω) (observedFiniteHistory (forgetPayloadConfiguration ω) t)=
      payloadObservedHistory ω t := by
  have h := conditionalPayloadHistory_eq_array_past (id : ℝ × T → ℝ × T) measurable_id
    (forgetPayloadConfiguration ω) (payloadTagSequence t0 ω) hClock t
  rw [assigned_forget_payloadTagSequence] at h
  change (chronologicalTaggedHistory (payloadTagSequence t0 ω)
    (observedFiniteHistory (forgetPayloadConfiguration ω) t)).map id=payloadObservedHistory ω t at h
  rw [Measure.map_id] at h
  exact h

variable {n : ℕ} {Seed U T : Type*} [MeasurableSpace U] [MeasurableSpace T]

lemma TaggedHybridRule.sampleTags_individual_payload_action (π : TaggedHybridRule n Seed T)
    (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : PayloadConfiguration T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (i : Fin n) :
    (π.sampleTags.asFinitePolicy ω.1).action (r,payloadTagSequence t0 ω) Finset.univ
      (combinedValues x (forgetPayloadConfiguration ω).2) (combinedClocks u (forgetPayloadConfiguration ω).2) (i.castAdd ω.1)=
        π.individual r (u i) i (x i) (Model.history Finset.univ x u (u i)) (payloadObservedHistory ω (u i)) := by
  rw [HybridRule.individual_action]
  change π.individual r (u i) i (x i) (Model.history Finset.univ x u (u i))
    (chronologicalTaggedHistory (payloadTagSequence t0 ω) (observedFiniteHistory (forgetPayloadConfiguration ω) (u i)))=_
  rw [payloadObservedHistory_from_sequence t0 ω hClock]

lemma TaggedHybridRule.sampleTags_poisson_payload_action (π : TaggedHybridRule n Seed T)
    (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : PayloadConfiguration T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (j : Fin ω.1) :
    (π.sampleTags.asFinitePolicy ω.1).action (r,payloadTagSequence t0 ω) Finset.univ
      (combinedValues x (forgetPayloadConfiguration ω).2) (combinedClocks u (forgetPayloadConfiguration ω).2) (j.natAdd n)=
        π.poisson r (ω.2 j).1 (ω.2 j).2.1 (ω.2 j).2.2
          (Model.history Finset.univ x u (ω.2 j).1) (payloadObservedHistory ω (ω.2 j).1) := by
  rw [HybridRule.poisson_action]
  change π.poisson r (ω.2 j).1 (ω.2 j).2.1
    (payloadTagSequence t0 ω (finitePastRank (observedFiniteHistory (forgetPayloadConfiguration ω) (ω.2 j).1) (ω.2 j).1))
    (Model.history Finset.univ x u (ω.2 j).1)
    (chronologicalTaggedHistory (payloadTagSequence t0 ω) (observedFiniteHistory (forgetPayloadConfiguration ω) (ω.2 j).1))=_
  have hRank : finitePastRank (observedFiniteHistory (forgetPayloadConfiguration ω) (ω.2 j).1) (ω.2 j).1=
      (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val :=
    finitePastRank_observedHistory (forgetPayloadConfiguration ω) hClock j le_rfl
  rw [hRank,
    payloadTagSequence_at_rank t0 ω j,payloadObservedHistory_from_sequence t0 ω hClock]

lemma TaggedHybridRule.reconstructPayload_actions (π : TaggedHybridRule n Seed T)
    (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (us : ℕ → U)
    (F : ℝ × U → ℝ × T) (hF : Measurable F)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (k : Fin (n+ω.1)) :
    ((π.reconstructPayload F).asFinitePolicy ω.1).action (r,us) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k=
      (π.sampleTags.asFinitePolicy ω.1).action (r,payloadTagSequence t0 (chronologicalPayloadConfiguration F (ω,us))) Finset.univ
        (combinedValues x (forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))).2)
        (combinedClocks u (forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))).2) k := by
  let rich := chronologicalPayloadConfiguration F (ω,us)
  have hRichClock : Function.Injective (fun j : Fin rich.1 => (rich.2 j).1) := hClock
  dsimp only [chronologicalPayloadConfiguration,forgetPayloadConfiguration]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · have hOld := π.sampleTags_individual_payload_action t0 r x u rich hRichClock i
    dsimp only [rich,chronologicalPayloadConfiguration,forgetPayloadConfiguration] at hOld
    rw [HybridRule.individual_action]
    refine Eq.trans ?_ hOld.symm
    change π.individual r (u i) i (x i) (Model.history Finset.univ x u (u i))
      (conditionalPayloadHistory F us (observedFiniteHistory ω (u i)))=_
    rw [conditionalPayloadHistory_eq_array_past F hF ω us hClock (u i)]
    rfl
  · have hOld := π.sampleTags_poisson_payload_action t0 r x u rich hRichClock j
    dsimp only [rich,chronologicalPayloadConfiguration,forgetPayloadConfiguration] at hOld
    rw [HybridRule.poisson_action]
    refine Eq.trans ?_ hOld.symm
    change π.poisson r (ω.2 j).1
      (F ((ω.2 j).2,us (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1))).1
      (F ((ω.2 j).2,us (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1))).2
      (Model.history Finset.univ x u (ω.2 j).1)
      (conditionalPayloadHistory F us (observedFiniteHistory ω (ω.2 j).1))=_
    rw [conditionalCurrentPayload_eq_array F ω us hClock j,
      conditionalPayloadHistory_eq_array_past F hF ω us hClock (ω.2 j).1]
    rfl

end ProphetSecretary.Limiting
