import ProphetSecretary.Limiting.TaggedHybridPrefixExecution
import ProphetSecretary.Limiting.ChronologicalPoissonPayload
import ProphetSecretary.Probability.CountableMixtureMeasurability

/-!
# Analytical evaluation of tagged hybrid configurations

A payload configuration stores only actual points and their occurrence tags.
The chronological sequence reconstructed below is an analytical evaluation
device. Prefix invariance proves that no unused tail or configuration count
can affect the executed callbacks.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

noncomputable def forgetPayloadConfiguration {T : Type*} (ω : PayloadConfiguration T) : Configuration :=
  ⟨ω.1,fun j => ((ω.2 j).1,(ω.2 j).2.1)⟩

lemma measurable_forgetPayloadConfiguration {T : Type*} [MeasurableSpace T] :
    Measurable (forgetPayloadConfiguration (T := T)) := by
  apply ProphetSecretary.Probability.measurable_of_sigma_branches
  intro N
  exact (measurable_configuration_mk N).comp
    (measurable_pi_lambda _ (fun j => ((measurable_pi_apply j).fst).prodMk (measurable_pi_apply j).snd.fst))

noncomputable def payloadTagSequence {T : Type*} (t0 : T) (ω : PayloadConfiguration T) (k : ℕ) : T :=
  if hk : k<ω.1 then
    (ω.2 ((Model.Instance.arrivalPermutation (fun j : Fin ω.1 => (ω.2 j).1)) ⟨k,hk⟩)).2.2 else t0

lemma measurable_payloadTagSequence {T : Type*} [MeasurableSpace T] (t0 : T) :
    Measurable (payloadTagSequence t0) := by
  apply measurable_pi_lambda
  intro k
  apply ProphetSecretary.Probability.measurable_of_sigma_branches
  intro N
  by_cases hk : k<N
  · change Measurable (fun v : Fin N → ℝ × (ℝ × T) =>
      if h : k<N then (v ((Model.Instance.arrivalPermutation (fun j : Fin N => (v j).1)) ⟨k,h⟩)).2.2 else t0)
    simp only [dif_pos hk]
    have hClock : Measurable (fun v : Fin N → ℝ × (ℝ × T) => fun j => (v j).1) :=
      measurable_pi_lambda _ (fun j => (measurable_pi_apply j).fst)
    have hPerm := Model.Instance.measurable_arrivalPermutation.comp hClock
    have hIndex : Measurable (fun v : Fin N → ℝ × (ℝ × T) =>
        (Model.Instance.arrivalPermutation (fun j : Fin N => (v j).1)) ⟨k,hk⟩) :=
      (measurable_of_countable (fun p : Equiv.Perm (Fin N) => p ⟨k,hk⟩)).comp hPerm
    have hEval : Measurable (fun z : (Fin N → ℝ × (ℝ × T)) × Fin N => z.1 z.2) :=
      measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
    exact (hEval.comp (measurable_id.prodMk hIndex)).snd.snd
  · change Measurable (fun v : Fin N → ℝ × (ℝ × T) =>
      if h : k<N then (v ((Model.Instance.arrivalPermutation (fun j : Fin N => (v j).1)) ⟨k,h⟩)).2.2 else t0)
    simp only [dif_neg hk]
    exact measurable_const

lemma forgetPayloadConfiguration_assigned {T : Type*} (ω : Configuration) (σ : ℕ → T) :
    forgetPayloadConfiguration (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,σ))=ω := by
  cases ω
  rfl

lemma payloadTagSequence_assigned_prefix {T : Type*} (t0 : T) (ω : Configuration) (σ : ℕ → T) (j : Fin ω.1) :
    payloadTagSequence t0 (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,σ)) j.val=σ j.val := by
  unfold payloadTagSequence
  dsimp only [chronologicalPayloadConfiguration]
  rw [dif_pos j.isLt]
  change σ ((Model.Instance.arrivalPermutation (fun k : Fin ω.1 => (ω.2 k).1)).symm
    ((Model.Instance.arrivalPermutation (fun k : Fin ω.1 => (ω.2 k).1)) j)).val=σ j.val
  rw [Equiv.symm_apply_apply]

lemma payloadTagSequence_at_rank {T : Type*} (t0 : T) (ω : PayloadConfiguration T) (j : Fin ω.1) :
    payloadTagSequence t0 ω (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val=(ω.2 j).2.2 := by
  unfold payloadTagSequence
  rw [dif_pos (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).isLt]
  change (ω.2 ((Model.Instance.arrivalPermutation (fun k : Fin ω.1 => (ω.2 k).1))
    ((Model.Instance.arrivalPermutation (fun k : Fin ω.1 => (ω.2 k).1)).symm j))).2.2=(ω.2 j).2.2
  rw [Equiv.apply_symm_apply]

lemma assigned_forget_payloadTagSequence {T : Type*} (t0 : T) (ω : PayloadConfiguration T) :
    chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T)
      (forgetPayloadConfiguration ω,payloadTagSequence t0 ω)=ω := by
  rcases ω with ⟨N,v⟩
  change payloadConfigurationMk N (fun j => ((v j).1,((v j).2.1,
      payloadTagSequence t0 ⟨N,v⟩ (Model.Instance.arrivalRank (fun k : Fin N => (v k).1) j).val)))=payloadConfigurationMk N v
  apply congrArg (payloadConfigurationMk N)
  funext j
  rw [payloadTagSequence_at_rank]

noncomputable def taggedHybridEvaluationWorld {n : ℕ} {Seed T : Type*} (t0 : T)
    (v : PayloadConfiguration T × Model.World n Seed) : HybridWorld n (Seed × (ℕ → T)) :=
  (forgetPayloadConfiguration v.1,(v.2.1,(v.2.2.1,(v.2.2.2,payloadTagSequence t0 v.1))))

lemma measurable_taggedHybridEvaluationWorld {n : ℕ} {Seed T : Type*} [MeasurableSpace Seed] [MeasurableSpace T]
    (t0 : T) : Measurable (taggedHybridEvaluationWorld (n := n) (Seed := Seed) t0) := by
  have hCfg := measurable_forgetPayloadConfiguration (T := T)
  have hTag := measurable_payloadTagSequence t0
  exact (hCfg.comp measurable_fst).prodMk
    (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk
      (measurable_snd.snd.snd.prodMk (hTag.comp measurable_fst))))

noncomputable def TaggedHybridRule.payloadReward {n : ℕ} {Seed T : Type*} [MeasurableSpace T]
    (π : TaggedHybridRule n Seed T) (t0 : T) (v : PayloadConfiguration T × Model.World n Seed) : ℝ :=
  π.sampleTags.realizedReward 0 (taggedHybridEvaluationWorld t0 v)

noncomputable def TaggedHybridRule.payloadDuration {n : ℕ} {Seed T : Type*} [MeasurableSpace T]
    (π : TaggedHybridRule n Seed T) (t0 : T) (v : PayloadConfiguration T × Model.World n Seed) : ℝ :=
  π.sampleTags.realizedDuration (taggedHybridEvaluationWorld t0 v)

lemma TaggedHybridRule.measurable_payloadReward {n : ℕ} {Seed T : Type*}
    [MeasurableSpace Seed] [MeasurableSpace T] (π : TaggedHybridRule n Seed T)
    (hπ : π.IsMeasurable) (t0 : T) : Measurable (π.payloadReward t0) :=
  (π.sampleTags.measurable_realizedReward (π.sampleTags_isMeasurable hπ) 0).comp
    (measurable_taggedHybridEvaluationWorld t0)

lemma TaggedHybridRule.measurable_payloadDuration {n : ℕ} {Seed T : Type*}
    [MeasurableSpace Seed] [MeasurableSpace T] (π : TaggedHybridRule n Seed T)
    (hπ : π.IsMeasurable) (t0 : T) : Measurable (π.payloadDuration t0) :=
  (π.sampleTags.measurable_realizedDuration (π.sampleTags_isMeasurable hπ)).comp
    (measurable_taggedHybridEvaluationWorld t0)

lemma TaggedHybridRule.payload_outcomes_assigned {n : ℕ} {Seed T : Type*} [MeasurableSpace T]
    (π : TaggedHybridRule n Seed T) (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (σ : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) :
    π.payloadReward t0 (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,σ),(x,(u,r)))=
      π.sampleTags.reward 0 (r,σ) x u ω ∧
    π.payloadDuration t0 (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,σ),(x,(u,r)))=
      π.sampleTags.stoppingTime (r,σ) x u ω := by
  have h := π.sampleTags_outcomes_eq_of_prefix r x u ω
    (payloadTagSequence t0 (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,σ))) σ hClock
    (payloadTagSequence_assigned_prefix t0 ω σ)
  change π.sampleTags.reward 0 _ x u (forgetPayloadConfiguration _)=_ ∧
    π.sampleTags.stoppingTime _ x u (forgetPayloadConfiguration _)=_
  rw [forgetPayloadConfiguration_assigned]
  exact h

end ProphetSecretary.Limiting
