import ProphetSecretary.Limiting.MappedFinitePotentialPolicy
import ProphetSecretary.Limiting.HybridZeroSimulation

/-!
# Concrete rules that accept only positive excess values

This property is used for the constructed lower-comparison policies. It is
proved for the shared mapped potential rule and preserved by causal virtual-zero
simulation. The competing-policy upper comparison remains over all rules.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*}

def HybridRule.AcceptsPositiveExcess (π : HybridRule n Seed) (a : ℝ) : Prop :=
  (∀ r t i x H Ξ, π.individual r t i x H Ξ = true → 0 < Model.excessValueMap a x) ∧
    (∀ r t x H Ξ, π.poisson r t x H Ξ = true → 0 < Model.excessValueMap a x)

lemma mappedPositivePotentialRule_acceptsPositiveExcess (Q : Model.Instance n) (a w c : ℝ) :
    (mappedPositivePotentialRule Q a w c).AcceptsPositiveExcess a := by
  constructor
  · intro r t i x H Ξ h
    exact (of_decide_eq_true h).1
  · intro r t x H Ξ h
    exact (of_decide_eq_true h).1

lemma HybridZeroSimulation.simulate_acceptsPositiveExcess (π : HybridRule (n + k) Seed) (a : ℝ)
    (hπ : π.AcceptsPositiveExcess a) : (HybridZeroSimulation.simulate π).AcceptsPositiveExcess a := by
  constructor
  · intro rz t i x H Ξ h
    exact hπ.1 rz.1 t (i.castAdd k) x (Model.ZeroSimulation.augmentedHistory H rz.2 t) Ξ h
  · intro rz t x H Ξ h
    exact hπ.2 rz.1 t x (Model.ZeroSimulation.augmentedHistory H rz.2 t) Ξ h

lemma HybridRule.asFinitePolicy_selected_positiveExcess (π : HybridRule n Seed) (a : ℝ)
    (hπ : π.AcceptsPositiveExcess a) (N : ℕ) (r : Seed) (x u : Fin (n + N) → ℝ) (i : Fin (n + N))
    (hi : (π.asFinitePolicy N).ActualSelects r Finset.univ x u i) : 0 < Model.excessValueMap a (x i) := by
  have ha := ((π.asFinitePolicy N).mem_accepted r Finset.univ x u i).mp hi.1.1 |>.2
  change Fin.addCases (fun j => π.individual r (u i) j (x i)
      (retainedHistory (Model.history Finset.univ x u (u i))) (poissonHistory (Model.history Finset.univ x u (u i))))
    (fun _ => π.poisson r (u i) (x i)
      (retainedHistory (Model.history Finset.univ x u (u i))) (poissonHistory (Model.history Finset.univ x u (u i)))) i = true at ha
  induction i using Fin.addCases with
  | left j =>
    simp only [Fin.addCases_left] at ha
    exact hπ.1 r _ j _ _ _ ha
  | right j =>
    simp only [Fin.addCases_right] at ha
    exact hπ.2 r _ _ _ _ ha

lemma HybridRule.reward_eq_terminal_add_excess (π : HybridRule n Seed) {a : ℝ} (ha : 0 ≤ a)
    (hπ : π.AcceptsPositiveExcess a) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) :
    π.reward a r x u ω = a + Model.excessValueMap a (π.reward 0 r x u ω) := by
  by_cases hs : π.HasSelection r x u ω
  · obtain ⟨i,hi⟩ := hs
    have hp := π.asFinitePolicy_selected_positiveExcess a hπ ω.1 r (combinedValues x ω.2) (combinedClocks u ω.2) i hi
    simp only [HybridRule.reward,show π.HasSelection r x u ω from ⟨i,hi⟩,if_true]
    rw [(π.asFinitePolicy ω.1).reward_eq_of_actualSelects _ _ _ _ hi]
    exact Model.positive_excess_reconstructs_value ha hp
  · simp only [HybridRule.reward,hs,if_false,Model.excessValueMap_zero ha,add_zero]

end ProphetSecretary.Limiting
