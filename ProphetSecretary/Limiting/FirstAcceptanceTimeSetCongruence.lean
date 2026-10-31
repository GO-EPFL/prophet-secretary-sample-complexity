import ProphetSecretary.Limiting.FirstAcceptanceSingleAddition

/-!
# Duration depends only on the set of accepted physical times

Relabeling occurrences may change the label chosen at a tied time, but not
the attained first physical time. Equality of accepted-time sets preserves
existence of an attained first point and the terminal default when none exists.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting.FirstAcceptance
variable {Ω Ξ : Type*}

theorem stoppingTime_eq_of_accepted_times_eq
    {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ}
    (hAB : ∀ i, A ω i → ∃ j, B ξ j ∧ u ω i=v ξ j)
    (hBA : ∀ j, B ξ j → ∃ i, A ω i ∧ v ξ j=u ω i) :
    stoppingTime A u ω=stoppingTime B v ξ := by
  by_cases hFirst : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := hFirst
    obtain ⟨j,hj,hTime⟩ := hAB i hi.1
    have hMin (k : ℕ) (hk : B ξ k) : v ξ j≤v ξ k := by
      obtain ⟨l,hl,hClock⟩ := hBA k hk
      exact hTime.symm.trans_le ((hi.2 l hl).1.trans_eq hClock.symm)
    obtain ⟨l,hl,hTimeL⟩ := exists_earliest_of_minimum_time hj hMin
    rw [stoppingTime_of_earliest hi,stoppingTime_of_earliest hl,hTimeL,hTime]
  · have hNone : ¬∃ j, Earliest B v ξ j := by
      rintro ⟨j,hj⟩
      obtain ⟨i,hi,hTime⟩ := hBA j hj.1
      have hMin (k : ℕ) (hk : A ω k) : u ω i≤u ω k := by
        obtain ⟨l,hl,hClock⟩ := hAB k hk
        exact hTime.symm.trans_le ((hj.2 l hl).1.trans_eq hClock.symm)
      obtain ⟨l,hl,_⟩ := exists_earliest_of_minimum_time hi hMin
      exact hFirst ⟨l,hl⟩
    rw [stoppingTime_of_no_first hFirst,stoppingTime_of_no_first hNone]

end ProphetSecretary.Limiting.FirstAcceptance
