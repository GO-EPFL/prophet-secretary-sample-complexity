import ProphetSecretary.Limiting.TaggedHybridDisplayRule
import ProphetSecretary.Limiting.PoissonPayloadDisplayHistory
import ProphetSecretary.Limiting.TaggedHybridPayloadActions

/-!
# Exact recovery of an ordinary displayed-value policy

Forward display after conditional old-payload reconstruction restores every
actual observed value and strict-past measure. Thus a general displayed-law
policy has exactly the same actions and outcomes after this causal round trip.
No injectivity of the display map is assumed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed U T : Type*} [MeasurableSpace U] [MeasurableSpace T]

lemma display_conditionalPayloadHistory_eq_past (F : ℝ × U → ℝ × T) (hF : Measurable F)
    (g : ℝ × T → ℝ) (hg : Measurable g) (ω : Configuration) (us : ℕ → U)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (hGraph : ∀ j : Fin ω.1, g (F ((ω.2 j).2,us (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val))=(ω.2 j).2)
    (t : ℝ) :
    (conditionalPayloadHistory F us (observedFiniteHistory ω t)).map (displayPayloadPoint g)=observedHistory ω t := by
  rw [conditionalPayloadHistory_eq_array_past F hF ω us hClock t,display_payloadObservedHistory g hg,
    display_conditionalPayloadConfiguration_eq_self F g ω us hGraph]

lemma HybridRule.observePayload_reconstruct_actions (π : HybridRule n Seed)
    (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (us : ℕ → U)
    (F : ℝ × U → ℝ × T) (hF : Measurable F) (g : ℝ × T → ℝ) (hg : Measurable g)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (hGraph : ∀ j : Fin ω.1, g (F ((ω.2 j).2,us (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val))=(ω.2 j).2)
    (k : Fin (n+ω.1)) :
    (((π.observePayload g).reconstructPayload F).asFinitePolicy ω.1).action (r,us) Finset.univ
      (combinedValues x ω.2) (combinedClocks u ω.2) k=
      (π.asFinitePolicy ω.1).action r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [HybridRule.individual_action,HybridRule.individual_action]
    change π.individual r (u i) i (x i) (Model.history Finset.univ x u (u i))
      ((conditionalPayloadHistory F us (observedFiniteHistory ω (u i))).map (displayPayloadPoint g))=_
    rw [display_conditionalPayloadHistory_eq_past F hF g hg ω us hClock hGraph]
    rfl
  · rw [HybridRule.poisson_action,HybridRule.poisson_action]
    change π.poisson r (ω.2 j).1
      (g (F ((ω.2 j).2,us (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1))))
      (Model.history Finset.univ x u (ω.2 j).1)
      ((conditionalPayloadHistory F us (observedFiniteHistory ω (ω.2 j).1)).map (displayPayloadPoint g))=_
    rw [finitePastRank_observedHistory ω hClock j le_rfl,hGraph j,
      display_conditionalPayloadHistory_eq_past F hF g hg ω us hClock hGraph]
    rfl

lemma HybridRule.observePayload_reconstruct_outcomes (π : HybridRule n Seed)
    (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (us : ℕ → U)
    (F : ℝ × U → ℝ × T) (hF : Measurable F) (g : ℝ × T → ℝ) (hg : Measurable g)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (hGraph : ∀ j : Fin ω.1, g (F ((ω.2 j).2,us (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val))=(ω.2 j).2) :
    ((π.observePayload g).reconstructPayload F).reward 0 (r,us) x u ω=π.reward 0 r x u ω ∧
      ((π.observePayload g).reconstructPayload F).stoppingTime (r,us) x u ω=π.stoppingTime r x u ω := by
  have h := (((π.observePayload g).reconstructPayload F).asFinitePolicy ω.1).outcomes_eq_of_actions_eq
    (π.asFinitePolicy ω.1) (r,us) r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2)
    (π.observePayload_reconstruct_actions r x u ω us F hF g hg hClock hGraph)
  constructor
  · rw [HybridRule.reward_zero_eq_finite,HybridRule.reward_zero_eq_finite]
    exact h.1
  · exact h.2

end ProphetSecretary.Limiting
