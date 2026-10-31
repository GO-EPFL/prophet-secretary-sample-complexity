import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Explicit arithmetic for the empirical-clock discrepancy bound

A depth of the fourth root of the sample size balances the small fourth-moment
term and the dyadic mesh. All numerical constants below are universal.
-/

open scoped BigOperators

namespace ProphetSecretary.Reach.EmpiricalChaining

lemma nat_square_le_twice_two_pow (J : ℕ) : (J : ℝ) ^ 2 ≤ 2 * (2 : ℝ) ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    by_cases hJ : 3 ≤ J
    · have hJr : (3 : ℝ) ≤ J := by exact_mod_cast hJ
      calc
        ((J + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (J : ℝ) ^ 2 := by push_cast; nlinarith
        _ ≤ 2 * (2 * (2 : ℝ) ^ J) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 2 * (2 : ℝ) ^ (J + 1) := by rw [pow_succ]; ring
    · have : J ≤ 2 := by omega
      interval_cases J <;> norm_num

lemma dyadic_geometric_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range J, ((7 : ℝ) / 8) ^ j) ≤ 8 := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := J)
    (x := (7 : ℝ) / 8) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Sum the explicit level bounds and mesh, with a depth between `r` and `r+1`. -/
lemma dyadic_root_cost_le {r : ℝ} (hr : 1 ≤ r) (J : ℕ)
    (hJlo : r ≤ (J : ℝ)) (hJhi : (J : ℝ) ≤ r + 1) :
    (∑ j ∈ Finset.range J, (2 * ((7 : ℝ) / 8) ^ j / r ^ 2 + 1 / r ^ 3)) +
      1 / (2 : ℝ) ^ J ≤ 20 / r ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsq : 0 < r ^ 2 := pow_pos hr0 2
  have hsum1 : (∑ j ∈ Finset.range J, 2 * ((7 : ℝ) / 8) ^ j / r ^ 2) ≤ 16 / r ^ 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    exact div_le_div_of_nonneg_right
      (by have h := dyadic_geometric_sum_le J; linarith) hsq.le
  have hJtwo : (J : ℝ) ≤ 2 * r := by linarith
  have hsum2 : (∑ _j ∈ Finset.range J, 1 / r ^ 3) ≤ 2 / r ^ 2 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hr0 3) hsq).mpr
    nlinarith [mul_le_mul_of_nonneg_right hJtwo hsq.le]
  have hmesh : 1 / (2 : ℝ) ^ J ≤ 2 / r ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) J) hsq).mpr
    have hrJ : r ^ 2 ≤ (J : ℝ) ^ 2 :=
      pow_le_pow_left₀ hr0.le hJlo 2
    simpa only [one_mul] using hrJ.trans (nat_square_le_twice_two_pow J)
  rw [Finset.sum_add_distrib]
  calc
    _ ≤ 16 / r ^ 2 + 2 / r ^ 2 + 2 / r ^ 2 := add_le_add (add_le_add hsum1 hsum2) hmesh
    _ = 20 / r ^ 2 := by ring

/-- The explicit constant in terms of the original number of independent clocks. -/
lemma dyadic_root_cost_le_sqrt (N : ℕ) (hN : 0 < N) :
    let r := Real.sqrt (Real.sqrt (N : ℝ))
    let J := Nat.ceil r
    (∑ j ∈ Finset.range J, (2 * ((7 : ℝ) / 8) ^ j / r ^ 2 + 1 / r ^ 3)) +
      1 / (2 : ℝ) ^ J ≤ 20 / Real.sqrt (N : ℝ) := by
  dsimp
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hNr
  have hr : 1 ≤ Real.sqrt (Real.sqrt (N : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hs
  have h := dyadic_root_cost_le hr (Nat.ceil (Real.sqrt (Real.sqrt (N : ℝ))))
    (Nat.le_ceil _) (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  simpa only [Real.sq_sqrt (Real.sqrt_nonneg _)] using h

end ProphetSecretary.Reach.EmpiricalChaining
