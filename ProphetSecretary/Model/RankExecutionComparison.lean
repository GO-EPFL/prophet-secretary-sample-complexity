import ProphetSecretary.Model.RankPolicy

/-! # Rank execution is determined by its analytical acceptance decisions -/

open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {A B : Type*}

lemma RankPolicy.accepted_eq_of_actions (π : RankPolicy A n) (ρ : RankPolicy B n)
    (r : A) (s : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action r p x i=ρ.action s p x i) : π.accepted r p x=ρ.accepted s p x := by
  ext i
  simp only [RankPolicy.mem_accepted,h i]

lemma RankPolicy.reaches_iff_of_actions (π : RankPolicy A n) (ρ : RankPolicy B n)
    (r : A) (s : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action r p x i=ρ.action s p x i) (i : Fin n) :
    π.Reaches r p x i ↔ ρ.Reaches s p x i := by
  unfold RankPolicy.Reaches
  rw [π.accepted_eq_of_actions ρ r s p x h]

lemma RankPolicy.selects_iff_of_actions (π : RankPolicy A n) (ρ : RankPolicy B n)
    (r : A) (s : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action r p x i=ρ.action s p x i) (i : Fin n) :
    π.Selects r p x i ↔ ρ.Selects s p x i := by
  unfold RankPolicy.Selects
  rw [π.reaches_iff_of_actions ρ r s p x h,π.accepted_eq_of_actions ρ r s p x h]

lemma RankPolicy.reward_eq_of_actions (π : RankPolicy A n) (ρ : RankPolicy B n)
    (r : A) (s : B) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (h : ∀ i, π.action r p x i=ρ.action s p x i) : π.reward r p x=ρ.reward s p x := by
  unfold RankPolicy.reward
  apply Finset.sum_congr rfl
  intro i _
  rw [π.selects_iff_of_actions ρ r s p x h]

end ProphetSecretary.Model
