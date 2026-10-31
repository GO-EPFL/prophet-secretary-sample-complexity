import ProphetSecretary.Model.TerminalReward

/-!
# Applying a zero-preserving function to the selected reward

At most one offer is selected, and the reward is zero on no selection. Thus a
common value map fixing zero can be applied after the reward is selected. This
is an analytical identity and does not replace any observed history values.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.mappedReward_eq_map_reward (π : Policy Seed n) (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.mappedReward (fun _ => f) r D x u = f (π.reward r D x u) := by
  by_cases hs : ∃ i, π.ActualSelects r D x u i
  · obtain ⟨i,hi⟩ := hs
    rw [π.mappedReward_eq_of_actualSelects _ r D x u hi,π.reward_eq_of_actualSelects r D x u hi]
  · have hn : ∀ i, ¬π.ActualSelects r D x u i := not_exists.mp hs
    rw [π.reward_eq_zero_of_no_actualSelection r D x u hn,hf0]
    unfold Policy.mappedReward
    simp only [hn, if_false, Finset.sum_const_zero]

lemma RandomizedPolicy.mappedScalarObjective_excess_eq_integral (π : RandomizedPolicy n)
    (P : Instance n) {a : ℝ} (ha : 0 ≤ a) (w c : ℝ) :
    π.mappedScalarObjective P (fun _ => excessValueMap a) w c =
      ∫ ω : π.World, w * excessValueMap a (π.realizedReward ω) + c * π.realizedDuration ω ∂P.worldLaw π.seedLaw := by
  unfold mappedScalarObjective
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    change w * π.rule.mappedReward (fun _ => excessValueMap a) ω.2.2 Finset.univ ω.1 ω.2.1 + c * π.realizedDuration ω =
      w * excessValueMap a (π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1) + c * π.realizedDuration ω
    rw [π.rule.mappedReward_eq_map_reward (excessValueMap a) (excessValueMap_zero ha) ω.2.2 Finset.univ ω.1 ω.2.1]

end ProphetSecretary.Model
