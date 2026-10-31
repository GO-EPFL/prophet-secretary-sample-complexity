import ProphetSecretary.Model.TerminalScalarValue

/-!
# Zero reward weight with a fixed terminal reward

The terminal amount disappears from the payoff when w=0. The full policy
supremum therefore agrees with the ordinary duration-only value c, including
all no-selection and zero-offer histories.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.terminalScalarObjective_zero_rewardWeight (π : RandomizedPolicy n)
    (P : Instance n) (a c : ℝ) : π.terminalScalarObjective P a 0 c = π.scalarObjective P 0 c := by
  unfold terminalScalarObjective scalarObjective
  simp only [zero_mul,zero_add]

lemma optimalTerminalScalarValue_zero_rewardWeight (P : Instance n) (a : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    optimalTerminalScalarValue P a 0 c = c := by
  have he : terminalScalarValues P a 0 c = {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P 0 c} := by
    ext v
    constructor
    · rintro ⟨π,rfl⟩
      exact ⟨π,π.terminalScalarObjective_zero_rewardWeight P a c⟩
    · rintro ⟨π,rfl⟩
      exact ⟨π,π.terminalScalarObjective_zero_rewardWeight P a c⟩
  calc
    _ = optimalScalarValue P 0 c := by unfold optimalTerminalScalarValue; rw [he]; rfl
    _ = c := optimalScalarValue_zero_rewardWeight P hc

end ProphetSecretary.Model
