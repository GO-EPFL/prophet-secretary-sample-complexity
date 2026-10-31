import ProphetSecretary.Analysis.EmpiricalLossRates

/-!
# Summing the earlier dyadic empirical-loss bands

The inverse first and fourth powers have geometric sums 2 and 16/15.
The resulting sum is at most 4x/k whenever the initial band a is at least
x≥1/k. All constants precede asymptotic notation and are dimension free.
-/

open Filter
open scoped BigOperators Topology

namespace ProphetSecretary.Analysis

lemma hasSum_empirical_dyadic_terms {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    HasSum (fun j : ℕ => 1 / (((2 : ℝ) ^ j * a) * k ^ 3) +
      1 / (((2 : ℝ) ^ j * a) ^ 4 * k ^ 6))
      (2 / (a * k ^ 3) + (16 / 15 : ℝ) / (a ^ 4 * k ^ 6)) := by
  have h1 : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j) 2 := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)) using 1
    norm_num
  have h4 : HasSum (fun j : ℕ => (1 / 16 : ℝ) ^ j) (16 / 15 : ℝ) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)) using 1
    norm_num
  have heq (j : ℕ) : 1 / (((2 : ℝ) ^ j * a) * k ^ 3) +
      1 / (((2 : ℝ) ^ j * a) ^ 4 * k ^ 6) =
      (1 / 2 : ℝ) ^ j * (1 / (a * k ^ 3)) + (1 / 16 : ℝ) ^ j * (1 / (a ^ 4 * k ^ 6)) := by
    have hpow : ((2 : ℝ) ^ j) ^ 4 = (16 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 4, pow_mul]
      norm_num
    rw [mul_pow, hpow]
    simp only [div_pow, one_pow]
    have h2 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have h16 : (16 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    field_simp
  have h := (h1.mul_right (1 / (a * k ^ 3))).add (h4.mul_right (1 / (a ^ 4 * k ^ 6)))
  simp_rw [← heq] at h
  have hr : 2 * (1 / (a * k ^ 3)) + (16 / 15 : ℝ) * (1 / (a ^ 4 * k ^ 6)) =
      2 / (a * k ^ 3) + (16 / 15 : ℝ) / (a ^ 4 * k ^ 6) := by ring
  rw [← hr]
  exact h

lemma empirical_dyadic_terms_sum_le {a k x : ℝ} (hk : 0 < k) (hxk : 1 / k ≤ x) (hxa : x ≤ a) :
    (∑' j : ℕ, (1 / (((2 : ℝ) ^ j * a) * k ^ 3) +
      1 / (((2 : ℝ) ^ j * a) ^ 4 * k ^ 6))) ≤ 4 * x / k := by
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have ha := hx.trans_le hxa
  rw [(hasSum_empirical_dyadic_terms ha hk).tsum_eq]
  have hfirst : 1 / (a * k ^ 3) ≤ 1 / (x * k ^ 3) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hxa (by positivity))
  have hp4 : x ^ 4 ≤ a ^ 4 := by gcongr
  have hfourth : 1 / (a ^ 4 * k ^ 6) ≤ 1 / (x ^ 4 * k ^ 6) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hp4 (by positivity))
  have hrate := empirical_far_terms_le hk hxk
  have hnonneg : 0 ≤ 1 / (x ^ 4 * k ^ 6) := by positivity
  have h16 : (16 / 15 : ℝ) ≤ 2 := by norm_num
  have hweighted := mul_le_mul_of_nonneg_right h16 hnonneg
  have h2 := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2)
  have h4 := mul_le_mul_of_nonneg_left hfourth (by norm_num : (0 : ℝ) ≤ 16 / 15)
  have htwo := mul_le_mul_of_nonneg_left hrate (by norm_num : (0 : ℝ) ≤ 2)
  have heq1 : 2 / (a * k ^ 3) = 2 * (1 / (a * k ^ 3)) := by ring
  have heq4 : (16 / 15 : ℝ) / (a ^ 4 * k ^ 6) = (16 / 15 : ℝ) * (1 / (a ^ 4 * k ^ 6)) := by ring
  rw [heq1, heq4]
  calc
    _ ≤ 2 * (1 / (x * k ^ 3)) + 2 * (1 / (x ^ 4 * k ^ 6)) :=
      add_le_add h2 (h4.trans hweighted)
    _ = 2 * (1 / (x * k ^ 3) + 1 / (x ^ 4 * k ^ 6)) := by ring
    _ ≤ 2 * (2 * x / k) := htwo
    _ = _ := by ring

end ProphetSecretary.Analysis
