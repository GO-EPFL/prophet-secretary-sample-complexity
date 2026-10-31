import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! # Finite weighted power inequality
A zero-valued dummy point completes subprobability weights to a probability
vector. Jensen then bounds powers of sums without a cardinality factor.
-/
open Set
open scoped BigOperators
namespace ProphetSecretary.Analysis

lemma weighted_sum_pow_le {ι : Type*} (s : Finset ι) (x β : ι → ℝ) {C : ℝ}
    (hC : 0 < C) (hβ : ∀ i ∈ s, 0 < β i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hSum : ∑ i ∈ s, β i ≤ C) (p : ℕ) (hp : 0 < p) :
    (∑ i ∈ s, x i) ^ p ≤ C ^ (p - 1) * ∑ i ∈ s, x i ^ p / β i ^ (p - 1) := by
  cases p with
  | zero => omega
  | succ k =>
    have hWeights : (∑ i ∈ s, β i / C) ≤ 1 := by rw [← Finset.sum_div]; exact (div_le_one hC).2 hSum
    have hJ := (convexOn_pow (k + 1) : ConvexOn ℝ (Ici (0 : ℝ)) (fun z : ℝ ↦ z ^ (k + 1))).map_add_sum_le
      (t := s) (w := fun i ↦ β i / C) (p := fun i ↦ C * x i / β i)
      (v := 1 - ∑ i ∈ s, β i / C) (q := (0 : ℝ))
      (fun i hi ↦ div_nonneg (hβ i hi).le hC.le) (by ring)
      (fun i hi ↦ div_nonneg (mul_nonneg hC.le (hx i hi)) (hβ i hi).le)
      (sub_nonneg.mpr hWeights) (by simp)
    simp only [smul_eq_mul, zero_pow (Nat.succ_ne_zero k), mul_zero, zero_add] at hJ
    have hLeft : (∑ i ∈ s, β i / C * (C * x i / β i)) = ∑ i ∈ s, x i := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [(hβ i hi).ne', hC.ne']
    rw [hLeft] at hJ
    simpa only [Nat.add_sub_cancel] using hJ.trans_eq (by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_pow, mul_pow, pow_succ]
      field_simp [(hβ i hi).ne', hC.ne']
      ring)

end ProphetSecretary.Analysis
