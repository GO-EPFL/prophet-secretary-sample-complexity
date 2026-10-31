import ProphetSecretary.Model.ValueResponseIntegrals

/-!
# Linearity of fixed-policy response

Only the perturbation changes here. All decisions remain those of the same
base policy, even when a perturbation is an analytical function of offer values.
-/

open MeasureTheory Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.mappedReward_add (π : Policy Seed n) (ψ φ : Fin n → ℝ → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.mappedReward (fun i a => ψ i a + φ i a) r D x u =
      π.mappedReward ψ r D x u + π.mappedReward φ r D x u := by
  unfold mappedReward
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma RandomizedPolicy.selectedResponse_add (π : RandomizedPolicy n) (P : Instance n)
    (ψ φ : Fin n → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hφ : ∀ i, Measurable (φ i))
    (hbψ : ∀ i a, |ψ i a| ≤ 1) (hbφ : ∀ i a, |φ i a| ≤ 1) :
    π.selectedResponse P (fun i a => ψ i a + φ i a) =
      π.selectedResponse P ψ + π.selectedResponse P φ := by
  unfold selectedResponse
  simp_rw [Policy.mappedReward_add]
  exact integral_add (π.integrable_selectedResponse P ψ hψ hbψ)
    (π.integrable_selectedResponse P φ hφ hbφ)

lemma Policy.mappedReward_one_eq_acceptanceIndicator (π : Policy Seed n)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.mappedReward (fun _ _ => 1) r D x u =
      if ∃ i, π.ActualSelects r D x u i then 1 else 0 := by
  by_cases hex : ∃ i, π.ActualSelects r D x u i
  · obtain ⟨i, hi⟩ := hex
    rw [if_pos ⟨i, hi⟩]
    unfold mappedReward
    rw [Finset.sum_eq_single i]
    · exact if_pos hi
    · intro j _ hji
      exact if_neg (fun hj => hji (π.actualSelects_unique r D x u hj hi))
    · simp
  · rw [if_neg hex]
    simp only [mappedReward, not_exists.mp hex, if_false, Finset.sum_const_zero]

end ProphetSecretary.Model
