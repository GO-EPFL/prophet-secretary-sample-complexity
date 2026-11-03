import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Hard sample counts for the calibrated learner

The bounded learner uses two blocks. Its outer reduction uses one cutoff
block and a dyadic-logarithmic scale pilot, as in `upouter:budget`.
-/

namespace ProphetSecretary.Statistics

/-- The scale pilot uses a multiple of five hundred full rounds. -/
def outerScalePilotRounds (m : ℕ) : ℕ := 6000 * Nat.clog 2 (2*m)

def calibratedSampleBudget (m : ℕ) : ℕ := 2*m

def calibratedOuterSampleBudget (m : ℕ) : ℕ := 3*m+outerScalePilotRounds m

lemma outerScalePilotRounds_eq (m : ℕ) :
    outerScalePilotRounds m = 6000 * Nat.ceil (Real.logb 2 (2*m : ℕ)) := by
  exact congrArg (fun q : ℕ => 6000*q) (Real.natCeil_logb_natCast 2 (2*m)).symm

lemma outerScalePilotRounds_rank (m : ℕ) :
    outerScalePilotRounds m = 500 * (12 * Nat.clog 2 (2*m)) := by
  unfold outerScalePilotRounds
  ring

private lemma twice_le_two_pow {m : ℕ} (hm : 1 ≤ m) : 2*m ≤ 2^m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hz : m = 0
    · subst m
      norm_num
    · have hmpos : 1 ≤ m := by omega
      have h := ih hmpos
      rw [pow_succ]
      omega

lemma clog_twice_le_self {m : ℕ} (hm : 1 ≤ m) : Nat.clog 2 (2*m) ≤ m :=
  Nat.clog_le_of_le_pow (twice_le_two_pow hm)

/-- An explicit instance-size-independent linear envelope for the hard budget. -/
theorem calibratedOuterSampleBudget_le {m : ℕ} (hm : 1 ≤ m) :
    calibratedOuterSampleBudget m ≤ 6003*m := by
  have h := Nat.mul_le_mul_left 6000 (clog_twice_le_self hm)
  unfold calibratedOuterSampleBudget outerScalePilotRounds
  omega

end ProphetSecretary.Statistics
