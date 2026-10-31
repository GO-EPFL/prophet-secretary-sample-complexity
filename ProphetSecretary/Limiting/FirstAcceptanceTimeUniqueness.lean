import ProphetSecretary.Limiting.CountableFirstAcceptance

/-!
# A selected occurrence is determined by its stopping time

Actual candidate clocks lie strictly before the terminal time and are
injective on present occurrences. The no-selection convention therefore
cannot coincide with the time of a selected occurrence.
-/

namespace ProphetSecretary.Limiting.FirstAcceptance

lemma selectedCode_eq_of_stoppingTime_eq {Ω : Type*}
    (A B : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) (present : ℕ → Prop)
    (hA : ∀ i, A ω i → present i) (hB : ∀ i, B ω i → present i)
    (hTime : ∀ i, present i → u ω i < 1)
    (hInjective : Set.InjOn (u ω) {i | present i})
    (hEqual : stoppingTime A u ω = stoppingTime B u ω) :
    selectedCode A u ω = selectedCode B u ω := by
  cases hCodeA : selectedCode A u ω with
  | zero =>
    cases hCodeB : selectedCode B u ω with
    | zero => rfl
    | succ j =>
      have hj := ((selectedCode_eq_succ_iff B u ω j).mp hCodeB).1
      have he : (1 : ℝ) = u ω j := by simpa [stoppingTime,hCodeA,hCodeB] using hEqual
      exact False.elim ((hTime j (hB j hj)).ne he.symm)
  | succ i =>
    have hi := ((selectedCode_eq_succ_iff A u ω i).mp hCodeA).1
    cases hCodeB : selectedCode B u ω with
    | zero =>
      have he : u ω i = (1 : ℝ) := by simpa [stoppingTime,hCodeA,hCodeB] using hEqual
      exact False.elim ((hTime i (hA i hi)).ne he)
    | succ j =>
      have hj := ((selectedCode_eq_succ_iff B u ω j).mp hCodeB).1
      have he : u ω i = u ω j := by simpa [stoppingTime,hCodeA,hCodeB] using hEqual
      exact congrArg Nat.succ (hInjective (hA i hi) (hB j hj) he)

end ProphetSecretary.Limiting.FirstAcceptance
