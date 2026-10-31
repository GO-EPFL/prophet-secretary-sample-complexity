import ProphetSecretary.Model.TerminalScalarValue

/-!
# The ordinary reward model is the zero-terminal specialization

Accepting a zero-valued offer and selecting nothing need not be distinguished
by reward when the terminal amount is zero. The main value and the auxiliary
fixed-terminal value then agree over exactly the same admissible policies.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.realizedTerminalReward_zero (π : RandomizedPolicy n) (ω : π.World) :
    π.realizedTerminalReward 0 ω = π.realizedReward ω := by
  by_cases hs : ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i
  · unfold realizedTerminalReward
    rw [if_pos hs]
  · unfold realizedTerminalReward
    rw [if_neg hs]
    exact (π.rule.reward_eq_zero_of_no_actualSelection _ _ _ _ (not_exists.mp hs)).symm

lemma RandomizedPolicy.terminalScalarObjective_zero_terminal (π : RandomizedPolicy n) (P : Instance n) (w c : ℝ) :
    π.terminalScalarObjective P 0 w c = π.scalarObjective P w c := by
  unfold terminalScalarObjective scalarObjective
  simp_rw [π.realizedTerminalReward_zero]

lemma optimalTerminalScalarValue_zero_terminal (P : Instance n) (w c : ℝ) :
    optimalTerminalScalarValue P 0 w c = optimalScalarValue P w c := by
  have he : terminalScalarValues P 0 w c = {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P w c} := by
    ext v
    constructor
    · rintro ⟨π,rfl⟩
      exact ⟨π,π.terminalScalarObjective_zero_terminal P w c⟩
    · rintro ⟨π,rfl⟩
      exact ⟨π,π.terminalScalarObjective_zero_terminal P w c⟩
  unfold optimalTerminalScalarValue
  rw [he]
  rfl

end ProphetSecretary.Model
