import ProphetSecretary.Limiting.FirstAcceptanceSingleAddition

/-!
# Duration after at most one new accepted occurrence

Old accepted clocks are preserved; the newly present code may have had a
different dummy clock while absent. Adding that one accepted occurrence
cannot destroy an attained first acceptance. This comparison also respects
the terminal default on exceptional configurations without an old first point.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting.FirstAcceptance
variable {Ω Ξ : Type*}

lemma stoppingTime_antitone_one_new_code
    {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ} (i : ℕ)
    (hAdd : ∀ k, A ω k → B ξ k)
    (hOther : ∀ k, k≠i → B ξ k → A ω k)
    (hTime : ∀ k, A ω k → v ξ k=u ω k)
    (hUpper : ∀ k, B ξ k → v ξ k≤1) :
    stoppingTime B v ξ ≤ stoppingTime A u ω := by
  by_cases hFirst : ∃ j, Earliest A u ω j
  · obtain ⟨j,hj⟩ := hFirst
    rw [stoppingTime_of_earliest hj]
    by_cases hI : B ξ i ∧ v ξ i<u ω j
    · have hMin (k : ℕ) (hk : B ξ k) : v ξ i≤v ξ k := by
        by_cases hki : k=i
        · subst k
          exact le_rfl
        · have hOld := hOther k hki hk
          exact hI.2.le.trans ((hj.2 k hOld).1.trans_eq (hTime k hOld).symm)
      obtain ⟨k,hk,hTimeK⟩ := exists_earliest_of_minimum_time hI.1 hMin
      rw [stoppingTime_of_earliest hk,hTimeK]
      exact hI.2.le
    · have hMin (k : ℕ) (hk : B ξ k) : v ξ j≤v ξ k := by
        rw [hTime j hj.1]
        by_cases hki : k=i
        · subst k
          exact le_of_not_gt (fun hLt => hI ⟨hk,hLt⟩)
        · have hOld := hOther k hki hk
          exact (hj.2 k hOld).1.trans_eq (hTime k hOld).symm
      obtain ⟨k,hk,hTimeK⟩ := exists_earliest_of_minimum_time (hAdd j hj.1) hMin
      rw [stoppingTime_of_earliest hk,hTimeK,hTime j hj.1]
  · rw [stoppingTime_of_no_first hFirst]
    exact stoppingTime_le_one hUpper

end ProphetSecretary.Limiting.FirstAcceptance
