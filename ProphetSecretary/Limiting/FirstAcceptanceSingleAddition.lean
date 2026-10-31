import ProphetSecretary.Limiting.CountableFirstAcceptance

/-!
# Actual first acceptance after adding one candidate

Adding a single accepted code cannot destroy an attained first point. This
controls actual stopping duration, including on raw configurations where an
unattained accepted set uses the terminal default. It is distinct from a
monotonicity claim for arbitrary infinite additions.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting.FirstAcceptance
variable {Ω : Type*}

lemma exists_earliest_of_minimum_time {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω} {i : ℕ}
    (hi : A ω i) (hMin : ∀ j, A ω j → u ω i ≤ u ω j) :
    ∃ j, Earliest A u ω j ∧ u ω j=u ω i := by
  have hex : ∃ j, A ω j ∧ u ω j=u ω i := ⟨i,hi,rfl⟩
  let j := Nat.find hex
  have hSpec := Nat.find_spec hex
  refine ⟨j,⟨hSpec.1,?_⟩,hSpec.2⟩
  intro k hk
  refine ⟨hSpec.2.trans_le (hMin k hk),?_⟩
  intro hTime
  exact Nat.find_min' hex ⟨hk,hTime.symm.trans hSpec.2⟩

lemma stoppingTime_antitone_single_addition {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    {ω ξ : Ω} (i : ℕ) (hClock : ∀ k, u ξ k=u ω k)
    (hAdd : ∀ k, A ω k → A ξ k)
    (hOther : ∀ k, k ≠ i → A ξ k → A ω k)
    (hUpper : ∀ k, A ξ k → u ξ k ≤ 1) : stoppingTime A u ξ ≤ stoppingTime A u ω := by
  by_cases hFirst : ∃ j, Earliest A u ω j
  · obtain ⟨j,hj⟩ := hFirst
    rw [stoppingTime_of_earliest hj]
    by_cases hI : A ξ i ∧ u ξ i < u ω j
    · have hMin (k : ℕ) (hk : A ξ k) : u ξ i ≤ u ξ k := by
        by_cases hki : k=i
        · subst k
          exact le_rfl
        · exact hI.2.le.trans ((hj.2 k (hOther k hki hk)).1.trans_eq (hClock k).symm)
      obtain ⟨k,hk,hTime⟩ := exists_earliest_of_minimum_time hI.1 hMin
      rw [stoppingTime_of_earliest hk,hTime]
      exact hI.2.le
    · have hMin (k : ℕ) (hk : A ξ k) : u ξ j ≤ u ξ k := by
        rw [hClock j]
        by_cases hki : k=i
        · subst k
          exact le_of_not_gt (fun hLt => hI ⟨hk,hLt⟩)
        · exact (hj.2 k (hOther k hki hk)).1.trans_eq (hClock k).symm
      obtain ⟨k,hk,hTime⟩ := exists_earliest_of_minimum_time (hAdd j hj.1) hMin
      rw [stoppingTime_of_earliest hk,hTime,hClock j]
  · rw [stoppingTime_of_no_first hFirst]
    exact stoppingTime_le_one hUpper

end ProphetSecretary.Limiting.FirstAcceptance
