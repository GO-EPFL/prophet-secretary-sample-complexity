import ProphetSecretary.Limiting.CountableIndividualOmission

/-!
# The omitted individual excess maximum controls every omitted value

The bound uses only the common cap. Its expectation and explicit tail-count
estimate were proved on the actual independent individual product law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma individualTailExcessMaximum_bounds_of_cap (B : CountableInstance) (N : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, x i ≤ (B.cap : ℝ)) : B.individualTailExcessMaximum N x ∈ Icc (0 : ℝ) B.cap := by
  have hc (k : ℕ) : Model.excessValueMap B.terminal (x (k+N)) ≤ (B.cap : ℝ) :=
    (Model.excessValueMap_le_self B.terminal.property _).trans (hx (k+N))
  exact ⟨terminal_le_countableMaximum B.cap.property B.cap.property _ hc,
    countableMaximum_le B.cap.property B.cap.property _ hc⟩

lemma individual_value_le_tail_level (B : CountableInstance) (N : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, x i ≤ (B.cap : ℝ)) (j : ℕ) (hj : N ≤ j) :
    x j ≤ B.individualTailExcessMaximum N x + (B.terminal : ℝ) := by
  have hc (k : ℕ) : Model.excessValueMap B.terminal (x (k+N)) ≤ (B.cap : ℝ) :=
    (Model.excessValueMap_le_self B.terminal.property _).trans (hx (k+N))
  have hm := le_countableMaximum B.cap.property B.cap.property
    (fun k => Model.excessValueMap B.terminal (x (k+N))) hc (j-N)
  rw [Nat.sub_add_cancel hj] at hm
  calc
    _ ≤ (B.terminal : ℝ) + Model.excessValueMap B.terminal (x j) := Model.value_le_terminal_add_excess _
    _ ≤ (B.terminal : ℝ) + B.individualTailExcessMaximum N x := add_le_add le_rfl hm
    _ = _ := add_comm _ _

end ProphetSecretary.Limiting.CountableInstance
