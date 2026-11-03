import ProphetSecretary.Statistics.PlannerWeights
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log

/-!
# Polynomial size of the planning weight after the empirical cutoff

The cutoff `4 ceil(log₂ m)+2` in `con:calibrated-learner` makes the
exponential weight a polynomial in the sample count. The explicit degree
below is only an upper bound; no optimal computational exponent is claimed.
-/

namespace ProphetSecretary.Statistics

lemma two_pow_clog_le_twice {m : ℕ} (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  by_cases hm1 : m = 1
  · simp [hm1]
  · have hm2 : 1 < m := by omega
    have hk := Nat.clog_pos (by decide : 1 < 2) hm2
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hm2
    calc
      2 ^ Nat.clog 2 m = 2 ^ (Nat.clog 2 m).pred * 2 := by
        rw [← pow_succ]
        exact congrArg (fun a : ℕ => 2 ^ a) (Nat.succ_pred_eq_of_pos hk).symm
      _ ≤ 2 * m := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 hp.le

/-- The normalized recursive planner has a dimension-free polynomial weight
on every empirical array passing its positive-count cutoff. -/
theorem plannerWeight_le_polynomial {ι : Type*} (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {m : ℕ} (hm : 1 ≤ m)
    (hcount : (∑ i ∈ A, p i) ≤ 4 * (Nat.clog 2 m : ℝ) + 2) :
    plannerWeight A p ≤ (4 : ℝ)^8 * (2 * (m : ℝ))^32 := by
  let k := Nat.clog 2 m
  have hpow : (2 : ℝ)^k ≤ 2 * (m : ℝ) := by
    exact_mod_cast two_pow_clog_le_twice hm
  calc
    plannerWeight A p ≤ Real.exp (4 * ∑ i ∈ A, p i) := plannerWeight_le_exp A p hp
    _ ≤ Real.exp (4 * (4 * (k : ℝ) + 2)) :=
      Real.exp_le_exp.mpr (by dsimp [k]; linarith)
    _ = (Real.exp 1)^(16*k+8) := by
      rw [show 4 * (4 * (k : ℝ) + 2) = ((16*k+8 : ℕ) : ℝ)*1 by push_cast; ring,
        Real.exp_nat_mul]
    _ ≤ (4 : ℝ)^(16*k+8) := pow_le_pow_left₀ (Real.exp_nonneg 1)
      (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4)) _
    _ = (4 : ℝ)^8 * ((2 : ℝ)^k)^32 := by
      rw [pow_add, mul_comm (4^_) (4^8), show (4 : ℝ) = 2^2 by norm_num]
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ (4 : ℝ)^8 * (2 * (m : ℝ))^32 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpow _) (by positivity)

end ProphetSecretary.Statistics
