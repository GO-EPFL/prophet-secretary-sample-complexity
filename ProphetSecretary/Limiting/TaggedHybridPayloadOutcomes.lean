import ProphetSecretary.Limiting.TaggedHybridPayloadActions
import ProphetSecretary.Model.SubexecutionComparison
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# Exact selected outcomes of the reconstructed hybrid policy

The old and displayed arrays have the same clocks. Action equality therefore
identifies the selected occurrence and stopping time. A displayed linear
amplitude changes only that selected anonymous reward.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed U T : Type*} [MeasurableSpace U] [MeasurableSpace T]

omit [MeasurableSpace U] [MeasurableSpace T] in
lemma combinedClocks_forget_conditionalPayload (u : Fin n → ℝ) (ω : Configuration)
    (us : ℕ → U) (F : ℝ × U → ℝ × T) :
    combinedClocks u (forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))).2=combinedClocks u ω.2 := by
  funext k
  refine Fin.addCases (fun _ => rfl) (fun _ => rfl) k

lemma TaggedHybridRule.reconstructPayload_selects_iff (π : TaggedHybridRule n Seed T)
    (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (us : ℕ → U)
    (F : ℝ × U → ℝ × T) (hF : Measurable F)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (k : Fin (n+ω.1)) :
    ((π.reconstructPayload F).asFinitePolicy ω.1).ActualSelects (r,us) Finset.univ
      (combinedValues x ω.2) (combinedClocks u ω.2) k ↔
      (π.sampleTags.asFinitePolicy ω.1).ActualSelects (r,payloadTagSequence t0 (chronologicalPayloadConfiguration F (ω,us))) Finset.univ
        (combinedValues x (forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))).2)
        (combinedClocks u (forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))).2) k := by
  let old := forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))
  let s := (r,payloadTagSequence t0 (chronologicalPayloadConfiguration F (ω,us)))
  have hU (j : Fin (n+ω.1)) : combinedClocks u old.2 j=combinedClocks u ω.2 j :=
    congrFun (combinedClocks_forget_conditionalPayload u ω us F) j
  have ha := π.reconstructPayload_actions t0 r x u ω us F hF hClock
  constructor
  · intro hk
    exact ((π.reconstructPayload F).asFinitePolicy ω.1).actualSelects_of_subexecution
      (π.sampleTags.asFinitePolicy ω.1) (OrderIso.refl _).toOrderEmbedding (r,us) s
      (combinedValues x ω.2) (combinedClocks u ω.2) (combinedValues x old.2) (combinedClocks u old.2)
      (fun j => (hU j).symm) (fun j => (ha j).symm) k hk
  · intro hk
    exact (π.sampleTags.asFinitePolicy ω.1).actualSelects_of_subexecution
      ((π.reconstructPayload F).asFinitePolicy ω.1) (OrderIso.refl _).toOrderEmbedding s (r,us)
      (combinedValues x old.2) (combinedClocks u old.2) (combinedValues x ω.2) (combinedClocks u ω.2)
      hU ha k hk

lemma TaggedHybridRule.reconstructPayload_duration (π : TaggedHybridRule n Seed T)
    (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (us : ℕ → U)
    (F : ℝ × U → ℝ × T) (hF : Measurable F)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) :
    (π.reconstructPayload F).stoppingTime (r,us) x u ω=
      π.payloadDuration t0 (chronologicalPayloadConfiguration F (ω,us),(x,(u,r))) := by
  let old := forgetPayloadConfiguration (chronologicalPayloadConfiguration F (ω,us))
  let s := (r,payloadTagSequence t0 (chronologicalPayloadConfiguration F (ω,us)))
  have hU (j : Fin (n+ω.1)) : combinedClocks u old.2 j=combinedClocks u ω.2 j :=
    congrFun (combinedClocks_forget_conditionalPayload u ω us F) j
  have ha := π.reconstructPayload_actions t0 r x u ω us F hF hClock
  have hForward := (π.sampleTags.asFinitePolicy ω.1).stoppingTime_le_of_subexecution
    ((π.reconstructPayload F).asFinitePolicy ω.1) (Equiv.refl (Fin (n+ω.1))).toEmbedding s (r,us)
    (combinedValues x old.2) (combinedClocks u old.2) (combinedValues x ω.2) (combinedClocks u ω.2) hU ha
  have hReverse := ((π.reconstructPayload F).asFinitePolicy ω.1).stoppingTime_le_of_subexecution
    (π.sampleTags.asFinitePolicy ω.1) (Equiv.refl (Fin (n+ω.1))).toEmbedding (r,us) s
    (combinedValues x ω.2) (combinedClocks u ω.2) (combinedValues x old.2) (combinedClocks u old.2)
    (fun j => (hU j).symm) (fun j => (ha j).symm)
  exact le_antisymm hReverse hForward

noncomputable def TaggedHybridRule.payloadSelectedAmplitude (π : TaggedHybridRule n Seed T)
    (t0 : T) (A : ℝ × T → ℝ) (v : PayloadConfiguration T × Model.World n Seed) : ℝ :=
  let old := forgetPayloadConfiguration v.1
  (π.sampleTags.asFinitePolicy v.1.1).selectedTag (v.2.2.2,payloadTagSequence t0 v.1)
    (combinedValues v.2.1 old.2) (combinedClocks v.2.2.1 old.2)
    (fun k => Fin.addCases (fun _ : Fin n => 0) (fun j : Fin v.1.1 => A (v.1.2 j).2) k)

lemma TaggedHybridRule.reconstructPayload_reward (π : TaggedHybridRule n Seed T)
    (t0 : T) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (us : ℕ → U)
    (F : ℝ × U → ℝ × T) (hF : Measurable F)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (A : ℝ × T → ℝ) (θ : ℝ)
    (hDisplay : ∀ j : Fin ω.1, (ω.2 j).2=
      ((chronologicalPayloadConfiguration F (ω,us)).2 j).2.1+θ*A ((chronologicalPayloadConfiguration F (ω,us)).2 j).2) :
    (π.reconstructPayload F).reward 0 (r,us) x u ω=
      π.payloadReward t0 (chronologicalPayloadConfiguration F (ω,us),(x,(u,r)))+
        θ*π.payloadSelectedAmplitude t0 A (chronologicalPayloadConfiguration F (ω,us),(x,(u,r))) := by
  let rich := chronologicalPayloadConfiguration F (ω,us)
  let old := forgetPayloadConfiguration rich
  let s := (r,payloadTagSequence t0 rich)
  let tag : Fin (n+ω.1) → ℝ := fun k => Fin.addCases (fun _ : Fin n => 0) (fun j : Fin ω.1 => A (rich.2 j).2) k
  have hValues (k : Fin (n+ω.1)) : combinedValues x ω.2 k=combinedValues x old.2 k+θ*tag k := by
    dsimp only [old,rich,forgetPayloadConfiguration,chronologicalPayloadConfiguration]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [combinedValues,Fin.addCases_left,tag,mul_zero,add_zero]
    · simp only [combinedValues,Fin.addCases_right,tag]
      change (ω.2 j).2=(rich.2 j).2.1+θ*A (rich.2 j).2
      exact hDisplay j
  have hSel := π.reconstructPayload_selects_iff t0 r x u ω us F hF hClock
  change (π.reconstructPayload F).reward 0 (r,us) x u ω=π.sampleTags.reward 0 s x u old+
    θ*(π.sampleTags.asFinitePolicy ω.1).selectedTag s (combinedValues x old.2) (combinedClocks u old.2) tag
  rw [HybridRule.reward_zero_eq_finite,HybridRule.reward_zero_eq_finite]
  change ((π.reconstructPayload F).asFinitePolicy ω.1).reward (r,us) Finset.univ
    (combinedValues x ω.2) (combinedClocks u ω.2)=
      (π.sampleTags.asFinitePolicy ω.1).reward s Finset.univ (combinedValues x old.2) (combinedClocks u old.2)+
        θ*(π.sampleTags.asFinitePolicy ω.1).selectedTag s (combinedValues x old.2) (combinedClocks u old.2) tag
  unfold Model.Policy.reward Model.Policy.selectedTag
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (π.sampleTags.asFinitePolicy ω.1).ActualSelects s Finset.univ (combinedValues x old.2) (combinedClocks u old.2) k
  · rw [if_pos hk,if_pos hk,if_pos ((hSel k).mpr hk)]
    exact hValues k
  · rw [if_neg hk,if_neg hk,if_neg (fun h => hk ((hSel k).mp h)),mul_zero,add_zero]

end ProphetSecretary.Limiting
