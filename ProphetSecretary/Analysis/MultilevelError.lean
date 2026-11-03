import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical bounds for multilevel scalar planning

The mean-square recursion in `alg:mlmc-mse` has a geometrically discounted
sum of paired errors. Its decay follows by tracking that sum together with
the error. No probabilistic property of the estimator is asserted here.
-/

open scoped BigOperators

namespace ProphetSecretary.Analysis

/-- A geometrically discounted finite convolution, with zero initial value. -/
def geometricConvolution (q : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q ^ (n - j) * f j

lemma geometricConvolution_zero (q : ℝ) (f : ℕ → ℝ) :
    geometricConvolution q f 0 = 0 := by
  simp [geometricConvolution]

lemma geometricConvolution_succ (q : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    geometricConvolution q f (n + 1) =
      q * (geometricConvolution q f n + f n) := by
  unfold geometricConvolution
  rw [Finset.sum_range_succ]
  have hsum : (∑ j ∈ Finset.range n, q ^ (n + 1 - j) * f j) =
      q * ∑ j ∈ Finset.range n, q ^ (n - j) * f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
    ring
  rw [hsum, show n + 1 - n = 1 by omega, pow_one]
  ring

/-- The scalar planner's mean-square recurrence implies `alg:mlmc-rate`.
Here `e n` denotes the squared error, not its square root. -/
theorem multilevel_error_decay (e : ℕ → ℝ) (hzero : e 0 ≤ 25)
    (hstep : ∀ n : ℕ,
      e (n + 1) ≤ (1 / 16 : ℝ) *
        (e n + (1 / 4 : ℝ) ^ (n + 1) +
          2 * geometricConvolution (1 / 4) (fun j => e (j + 1) + e j) n)) :
    ∀ n : ℕ, e n ≤ 25 * (1 / 2 : ℝ) ^ n := by
  have hpair : ∀ n : ℕ,
      e n ≤ 25 * (1 / 2 : ℝ) ^ n ∧
      geometricConvolution (1 / 4) (fun j => e (j + 1) + e j) n ≤
        (75 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      constructor
      · simpa using hzero
      · norm_num [geometricConvolution]
    | succ n ih =>
      have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
      have hq : (1 / 4 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) n
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n]
      have he : e (n + 1) ≤ 25 * (1 / 2 : ℝ) ^ (n + 1) := by
        have hs := hstep n
        rw [pow_succ]
        nlinarith [ih.1, ih.2]
      refine ⟨he, ?_⟩
      rw [geometricConvolution_succ, pow_succ]
      rw [pow_succ] at he
      nlinarith [ih.1, ih.2]
  intro n
  exact (hpair n).1

end ProphetSecretary.Analysis
