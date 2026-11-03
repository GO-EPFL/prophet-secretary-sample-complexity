import ProphetSecretary.Model.RankRandomized

/-!
# Equality of rank executions

Agreement on candidate actions gives agreement on the selected reward and
all reach events. All action comparisons use the same observed rank prefix.
-/

namespace ProphetSecretary.Model

variable {n : ℕ} {A B : Type*}

lemma RankPolicy.accepted_eq_of_actions_eq (π : RankPolicy A n) (σ : RankPolicy B n)
    (a : A) (b : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action a p x i=σ.action b p x i) :
    π.accepted a p x=σ.accepted b p x := by
  ext i
  simp only [RankPolicy.mem_accepted,h i]

lemma RankPolicy.reaches_iff_of_actions_eq (π : RankPolicy A n) (σ : RankPolicy B n)
    (a : A) (b : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action a p x i=σ.action b p x i) (i : Fin n) :
    π.Reaches a p x i ↔ σ.Reaches b p x i := by
  unfold RankPolicy.Reaches
  rw [π.accepted_eq_of_actions_eq σ a b p x h]

lemma RankPolicy.reward_eq_of_actions_eq (π : RankPolicy A n) (σ : RankPolicy B n)
    (a : A) (b : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action a p x i=σ.action b p x i) :
    π.reward a p x=σ.reward b p x := by
  unfold RankPolicy.reward
  apply Finset.sum_congr rfl
  intro i _
  have hi : π.Selects a p x i ↔ σ.Selects b p x i := by
    simp only [RankPolicy.Selects,π.accepted_eq_of_actions_eq σ a b p x h,
      π.reaches_iff_of_actions_eq σ a b p x h i]
  by_cases hπ : π.Selects a p x i
  · rw [if_pos hπ,if_pos (hi.mp hπ)]
  · rw [if_neg hπ,if_neg (fun hσ => hπ (hi.mpr hσ))]

end ProphetSecretary.Model
