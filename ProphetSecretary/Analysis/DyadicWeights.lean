import ProphetSecretary.Analysis.WeightedFinitePower
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Linarith

/-! # Summable weights for dyadic moment chaining -/
open scoped BigOperators
namespace ProphetSecretary.Analysis

lemma geometric_sum_le_inverse {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  have h := geom_sum_mul_neg r J
  linarith [pow_nonneg hr0 J]

lemma dyadic_weight_sum_le (J : ℕ) : ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j ≤ 4 := by
  have h := geometric_sum_le_inverse (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1) J
  norm_num at h
  exact h

lemma dyadic_moment_factor (j q : ℕ) :
    (2 : ℝ) ^ j * (1 / (2 : ℝ) ^ (j + 1)) ^ (q + 1) / ((3 / 4 : ℝ) ^ j) ^ q =
      (1 / 2 : ℝ) ^ (q + 1) * ((2 / 3 : ℝ) ^ q) ^ j := by
  have hRatio : (2 : ℝ) * (1 / 2 : ℝ) ^ (q + 1) / (3 / 4 : ℝ) ^ q = (2 / 3 : ℝ) ^ q := by
    rw [pow_succ]
    calc
      _ = (1 / 2 : ℝ) ^ q / (3 / 4 : ℝ) ^ q := by ring
      _ = ((1 / 2 : ℝ) / (3 / 4 : ℝ)) ^ q := (div_pow _ _ _).symm
      _ = _ := by norm_num
  rw [← one_div_pow, pow_right_comm (1 / 2 : ℝ) (j + 1) (q + 1),
    pow_right_comm (3 / 4 : ℝ) j q, pow_succ]
  calc
    _ = (1 / 2 : ℝ) ^ (q + 1) * ((2 * (1 / 2 : ℝ) ^ (q + 1)) / (3 / 4 : ℝ) ^ q) ^ j := by
      rw [div_pow (2 * (1 / 2 : ℝ) ^ (q + 1)) ((3 / 4 : ℝ) ^ q) j, mul_pow 2 ((1 / 2 : ℝ) ^ (q + 1)) j]
      ring
    _ = _ := by rw [hRatio]

lemma dyadic_weighted_factor_sum_le (p J : ℕ) (hp : 2 ≤ p) :
    (∑ j ∈ Finset.range J, (2 : ℝ) ^ j * (1 / (2 : ℝ) ^ (j + 1)) ^ p /
      ((3 / 4 : ℝ) ^ j) ^ (p - 1)) ≤ 3 := by
  have hExp : p = (p - 1) + 1 := by omega
  have hRatio : (2 / 3 : ℝ) ^ (p - 1) ≤ 2 / 3 := by
    have hqExp : p - 1 = (p - 1 - 1) + 1 := by omega
    rw [hqExp, pow_succ]
    exact mul_le_of_le_one_left (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) ≤ 1))
  calc
    _ ≤ ∑ j ∈ Finset.range J, (2 / 3 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      have hFactor := dyadic_moment_factor j (p - 1)
      rw [← hExp] at hFactor
      rw [hFactor]
      calc
        _ ≤ 1 * ((2 / 3 : ℝ) ^ (p - 1)) ^ j := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)) (by positivity)
        _ ≤ _ := by simpa only [one_mul] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ (p - 1)) hRatio j
    _ ≤ 3 := by
      have h := geometric_sum_le_inverse (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1) J
      norm_num at h
      exact h

lemma dyadic_chain_pow_le {J : ℕ} (a b : ℝ) (L : Fin J → ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : ∀ j, 0 ≤ L j) (p : ℕ) (hp : 0 < p) :
    (a + b + ∑ j : Fin J, L j) ^ p ≤ (6 : ℝ) ^ (p - 1) *
      (a ^ p + b ^ p + ∑ j : Fin J, L j ^ p / ((3 / 4 : ℝ) ^ j.val) ^ (p - 1)) := by
  let X : Option (Option (Fin J)) → ℝ := fun i ↦ i.elim a (fun k ↦ k.elim b L)
  let β : Option (Option (Fin J)) → ℝ := fun i ↦ i.elim 1 (fun k ↦ k.elim 1 (fun j ↦ (3 / 4 : ℝ) ^ j.val))
  have hβ : ∀ i, 0 < β i := by
    intro i
    cases i with
    | none => norm_num [β]
    | some i =>
      cases i with
      | none => norm_num [β]
      | some j =>
        change (0 : ℝ) < (3 / 4 : ℝ) ^ j.val
        exact pow_pos (by norm_num) _
  have hX : ∀ i, 0 ≤ X i := by intro i; cases i with | none => exact ha | some i => cases i with | none => exact hb | some j => exact hL j
  have hSum : ∑ i, β i ≤ 6 := by
    simp only [β, Fintype.sum_option, Option.elim_none, Option.elim_some]
    rw [Fin.sum_univ_eq_sum_range]
    linarith [dyadic_weight_sum_le J]
  have h := weighted_sum_pow_le Finset.univ X β (by norm_num : (0 : ℝ) < 6)
    (fun i _ ↦ hβ i) (fun i _ ↦ hX i) hSum p hp
  simpa [X, β, Fintype.sum_option, add_assoc] using h

end ProphetSecretary.Analysis
