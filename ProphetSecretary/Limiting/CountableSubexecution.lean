import ProphetSecretary.Limiting.CountableFirstAcceptance

/-!
# Pathwise deletion comparisons for attained countable executions

A retained acceptance set is a subset of the original one. Rejecting dominated
values ensures the new reward is at least the reserve, while preserving every
original acceptance above reserve plus e controls the reward loss by e. The
actual causal simulator must separately construct these acceptance relations.
-/

open Set
open scoped Classical

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*} {A B : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}

lemma stoppingTime_le_of_subexecution (hA : HasFirstIfAccepted A u ω) (hB : HasFirstIfAccepted B u ω)
    (huA : ∀ i, A ω i → u ω i ≤ 1) (huB : ∀ i, B ω i → u ω i ≤ 1)
    (hsub : ∀ i, B ω i → A ω i) : stoppingTime A u ω ≤ stoppingTime B u ω := by
  have h := (le_stoppingTime_iff hA huA (stoppingTime A u ω)).mp le_rfl
  exact (le_stoppingTime_iff hB huB _).mpr ⟨h.1,fun i hi => h.2 i (hsub i hi)⟩

lemma reward_ge_reserve (a : ℝ) (hvalues : ∀ i, A ω i → a ≤ x ω i) : a ≤ reward a A u x ω := by
  by_cases he : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := he
    rw [reward_of_earliest a hi]
    exact hvalues i hi.1
  · rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr he,if_pos rfl]

lemma earliest_of_subexecution {i : ℕ} (hi : Earliest A u ω i) (hBi : B ω i)
    (hsub : ∀ j, B ω j → A ω j) : Earliest B u ω i :=
  ⟨hBi,fun j hj => hi.2 j (hsub j hj)⟩

lemma reward_le_of_high_acceptance_preserved (a : ℝ) {e : ℝ} (he : 0 ≤ e)
    (hsub : ∀ i, B ω i → A ω i) (hnew : ∀ i, B ω i → a ≤ x ω i)
    (hkeep : ∀ i, A ω i → a + e < x ω i → B ω i) :
    reward a A u x ω ≤ reward a B u x ω + e := by
  have hreserve := reward_ge_reserve (u := u) a hnew
  by_cases hfirst : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := hfirst
    rw [reward_of_earliest a hi]
    by_cases hlarge : a + e < x ω i
    · have hBi := hkeep i hi.1 hlarge
      rw [reward_of_earliest a (earliest_of_subexecution hi hBi hsub)]
      exact le_add_of_nonneg_right he
    · exact (not_lt.mp hlarge).trans (add_le_add hreserve le_rfl)
  · rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr hfirst,if_pos rfl]
    exact hreserve.trans (le_add_of_nonneg_right he)

end ProphetSecretary.Limiting.FirstAcceptance
