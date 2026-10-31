import ProphetSecretary.Limiting.TaggedHybridRule
import ProphetSecretary.Limiting.ChronologicalHistoryCorrespondence
import ProphetSecretary.Model.ExecutionAgreement

/-!
# Only tags of actual finite anonymous occurrences affect execution

An array of N anonymous points uses only the first N chronological auxiliary
entries. Equality of those entries gives equality of every potential action,
selected reward and stopping time. The conclusion is for the general tagged
callbacks and preserves all retained identities, including zero arrivals.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed T : Type*} [MeasurableSpace T]

lemma chronologicalTaggedHistory_eq_of_tag_prefix (ω : Configuration) (σ σ' : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (hPrefix : ∀ j : Fin ω.1, σ j.val=σ' j.val) (t : ℝ) :
    chronologicalTaggedHistory σ (observedFiniteHistory ω t)=chronologicalTaggedHistory σ' (observedFiniteHistory ω t) := by
  rw [chronologicalTaggedHistory_eq_array_past ω σ hClock t,chronologicalTaggedHistory_eq_array_past ω σ' hClock t]
  unfold chronologicalObservedTagHistory
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω.2 j).1<t
  · rw [if_pos hj,if_pos hj,hPrefix (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j)]
  · rw [if_neg hj,if_neg hj]

lemma TaggedHybridRule.sampleTags_actions_eq_of_prefix (π : TaggedHybridRule n Seed T)
    (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (σ σ' : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (hPrefix : ∀ j : Fin ω.1, σ j.val=σ' j.val) (k : Fin (n+ω.1)) :
    (π.sampleTags.asFinitePolicy ω.1).action (r,σ) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k=
      (π.sampleTags.asFinitePolicy ω.1).action (r,σ') Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [HybridRule.individual_action,HybridRule.individual_action]
    change π.individual r (u i) i (x i) (Model.history Finset.univ x u (u i))
      (chronologicalTaggedHistory σ (observedFiniteHistory ω (u i)))=_
    rw [chronologicalTaggedHistory_eq_of_tag_prefix ω σ σ' hClock hPrefix (u i)]
    rfl
  · rw [HybridRule.poisson_action,HybridRule.poisson_action]
    change π.poisson r (ω.2 j).1 (ω.2 j).2
      (σ (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1))
      (Model.history Finset.univ x u (ω.2 j).1)
      (chronologicalTaggedHistory σ (observedFiniteHistory ω (ω.2 j).1))=_
    rw [finitePastRank_observedHistory ω hClock j le_rfl,hPrefix (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j),
      chronologicalTaggedHistory_eq_of_tag_prefix ω σ σ' hClock hPrefix (ω.2 j).1]
    change _=π.poisson r (ω.2 j).1 (ω.2 j).2
      (σ' (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1))
      (Model.history Finset.univ x u (ω.2 j).1) (chronologicalTaggedHistory σ' (observedFiniteHistory ω (ω.2 j).1))
    rw [finitePastRank_observedHistory ω hClock j le_rfl]

lemma HybridRule.reward_zero_eq_finite (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) :
    π.reward 0 r x u ω=(π.asFinitePolicy ω.1).reward r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) := by
  unfold HybridRule.reward
  by_cases h : π.HasSelection r x u ω
  · rw [if_pos h]
  · rw [if_neg h]
    exact ((π.asFinitePolicy ω.1).reward_eq_zero_of_no_actualSelection r Finset.univ (combinedValues x ω.2)
      (combinedClocks u ω.2) (fun k hk => h ⟨k,hk⟩)).symm

lemma TaggedHybridRule.sampleTags_outcomes_eq_of_prefix (π : TaggedHybridRule n Seed T)
    (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (σ σ' : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (hPrefix : ∀ j : Fin ω.1, σ j.val=σ' j.val) :
    π.sampleTags.reward 0 (r,σ) x u ω=π.sampleTags.reward 0 (r,σ') x u ω ∧
      π.sampleTags.stoppingTime (r,σ) x u ω=π.sampleTags.stoppingTime (r,σ') x u ω := by
  have h := (π.sampleTags.asFinitePolicy ω.1).outcomes_eq_of_actions_eq (π.sampleTags.asFinitePolicy ω.1)
    (r,σ) (r,σ') Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2)
    (π.sampleTags_actions_eq_of_prefix r x u ω σ σ' hClock hPrefix)
  constructor
  · rw [HybridRule.reward_zero_eq_finite,HybridRule.reward_zero_eq_finite]
    exact h.1
  · exact h.2

end ProphetSecretary.Limiting
