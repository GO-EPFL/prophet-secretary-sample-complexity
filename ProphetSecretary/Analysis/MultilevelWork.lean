import ProphetSecretary.Analysis.MultilevelError

/-!
# A hard work bound for the multilevel recursion

The work recurrence counts every recursive child, including both copies in
a paired difference. The resulting bound holds for a deterministic upper
bound on every execution, rather than only for expected work.
-/

namespace ProphetSecretary.Analysis

/-- An explicit geometric bound for the scalar planner's recursive work.
The sequence `C` may be any deterministic work bound satisfying the displayed
recurrence; establishing that recurrence for the algorithm is separate. -/
theorem multilevel_work_bound (C : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hzero : C 0 ≤ c)
    (hstep : ∀ n : ℕ, C (n + 1) ≤ c +
      geometricConvolution 4 (fun j => c + C j + if j = 0 then 0 else C (j - 1))
        (n + 1)) :
    ∀ n : ℕ, C n ≤ 4 * c * (16 : ℝ) ^ n := by
  have htriple : ∀ n : ℕ,
      C n ≤ 4 * c * (16 : ℝ) ^ n ∧
      geometricConvolution 4 (fun j => c + C j + if j = 0 then 0 else C (j - 1)) n ≤
        3 * c * (16 : ℝ) ^ n ∧
      (if n = 0 then 0 else C (n - 1)) ≤ 4 * c * (16 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, mul_one, geometricConvolution_zero, ite_true]
      exact ⟨by linarith, by linarith, by linarith⟩
    | succ n ih =>
      have hp : 1 ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hcp : c ≤ c * (16 : ℝ) ^ n := by nlinarith
      have hsum :
          geometricConvolution 4
            (fun j => c + C j + if j = 0 then 0 else C (j - 1)) (n + 1) ≤
            3 * c * (16 : ℝ) ^ (n + 1) := by
        rw [geometricConvolution_succ, pow_succ]
        nlinarith [ih.1, ih.2.1, ih.2.2]
      refine ⟨?_, hsum, ?_⟩
      · have hs := hstep n
        rw [pow_succ] at hsum ⊢
        nlinarith
      · simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        rw [pow_succ]
        nlinarith [ih.1]
  intro n
  exact (htriple n).1

end ProphetSecretary.Analysis
