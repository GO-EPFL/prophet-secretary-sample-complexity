import ProphetSecretary.Analysis.PosteriorIncrement

/-!
# An averaged posterior increment

The unit interval bounds give total squared movement at most one. A
deterministic index among m rounds therefore has movement at most 1/m.
This is the high-first-moment response's covariance estimate.
-/

open Set
open scoped BigOperators
namespace ProphetSecretary.Analysis

theorem exists_averaged_posterior_increment {m : ℕ} (hm : 0<m) (s : ℕ → ℝ)
    (hStart : 0≤s 0) (hEnd : s m≤1) :
    ∃ j<m, Real.sqrt (s (j+1)-s j)≤1/Real.sqrt (m : ℝ) := by
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr hm
  have hSum : (∑ j∈Finset.range m, (s (j+1)-s j))≤∑ _j∈Finset.range m, (1/(m : ℝ)) := by
    rw [Finset.sum_range_sub]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one_div_cancel hmR.ne']
    linarith only [hStart,hEnd]
  obtain ⟨j,hj,hΔ⟩ := Finset.exists_le_of_sum_le ⟨0,Finset.mem_range.mpr hm⟩ hSum
  refine ⟨j,Finset.mem_range.mp hj,?_⟩
  have h := Real.sqrt_le_sqrt hΔ
  simpa only [Real.sqrt_div (by norm_num : (0 : ℝ)≤1),Real.sqrt_one] using h

end ProphetSecretary.Analysis
