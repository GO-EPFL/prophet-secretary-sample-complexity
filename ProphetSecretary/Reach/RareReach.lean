import ProphetSecretary.Model.Learner
import Mathlib.Tactic.Linarith

/-!
# Pathwise ingredients of the rare-jackpot reach constraint

Reach cannot depend on the candidate value before that value is observed. A policy
on a bounded base instance can therefore earn a large added jackpot only when it
reaches that identity. The final statistical coupling uses the hard training budget.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {Seed : Type*} {n : ℕ}

/-- Changing an unseen candidate's value cannot affect whether it is reached. -/
theorem Policy.reaches_update_value (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (a : ℝ) (hi : u i ≤ 1) :
    π.Reaches r (Function.update x i a) u i ↔ π.Reaches r x u i := by
  rw [π.reaches_iff_le_pendingTime r _ u i hi, π.reaches_iff_le_pendingTime r x u i hi]
  have h := π.pendingTime_update r x u i a (u i)
  apply Eq.to_iff
  simpa only [Function.update_eq_self] using congrArg (fun t => u i ≤ t) h

/-- A bounded reward plus a reached jackpot is a pathwise upper bound on reward.
The right hand reach event is computed on the base vector, without its jackpot flag. -/
theorem Policy.reward_le_jackpot_reach (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (b : Bool) {H A : ℝ}
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hx : ∀ j, x j ≤ H) (hi : u i ≤ 1) :
    π.reward r Finset.univ (Function.update x i (if b then A else x i)) u ≤
      H + A * (if b = true ∧ π.Reaches r x u i then 1 else 0) := by
  let y := Function.update x i (if b then A else x i)
  have hright : H ≤ H + A * (if b = true ∧ π.Reaches r x u i then 1 else 0) := by
    split_ifs <;> nlinarith
  by_cases h : ∃ j, π.ActualSelects r Finset.univ y u j
  · obtain ⟨j, hj⟩ := h
    rw [π.reward_eq_of_actualSelects r Finset.univ y u hj]
    by_cases hji : j = i
    · subst j
      cases b with
      | false =>
        have hy : y i = x i := by simp [y]
        rw [hy]
        exact (hx i).trans hright
      | true =>
        have hr : π.Reaches r y u i := π.selects_implies_reaches _ _ _ hj.1
        have hrbase : π.Reaches r x u i :=
          (π.reaches_update_value r x u i A hi).mp hr
        simp only [hrbase, and_self, if_true, mul_one]
        have hy : y i = A := by simp [y]
        rw [hy]
        exact le_add_of_nonneg_left hH
    · have hy : y j = x j := Function.update_of_ne hji _ _
      rw [hy]
      exact (hx j).trans hright
  · rw [π.reward_eq_zero_of_no_actualSelection r Finset.univ y u (fun j hj => h ⟨j, hj⟩)]
    exact hH.trans hright

/-- An explicit linear error at every positive perturbation size vanishes as that
size tends to zero. This isolates the elementary last step of `lem:reach`. -/
theorem reach_of_arbitrarily_small_jackpot_error {q rho K : ℝ} (hK : 0 ≤ K)
    (h : ∀ p : ℝ, 0 < p → p ≤ 1 → rho ≤ q + K * p) : rho ≤ q := by
  by_contra hnot
  have hd : 0 < rho - q := sub_pos.mpr (lt_of_not_ge hnot)
  let p := min 1 ((rho - q) / (2 * (K + 1)))
  have hden : 0 < 2 * (K + 1) := by linarith
  have hp : 0 < p := lt_min zero_lt_one (div_pos hd hden)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hpd : p ≤ (rho - q) / (2 * (K + 1)) := min_le_right _ _
  have hpbound := (le_div_iff₀ hden).mp hpd
  have hmain := h p hp hp1
  nlinarith

end ProphetSecretary.Model
