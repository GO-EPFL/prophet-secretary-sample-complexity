import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Vanishing explicit reciprocal-rank error bounds
-/

open Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma reciprocal_rank_tendsto_zero (K : ℝ) :
    Tendsto (fun N : ℕ => 1/(K*(N+1 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/K)
  have he : (fun N : ℕ => 1/(K*(N+1 : ℕ))) = (fun N : ℕ => (1/K)*(1/((N : ℝ)+1))) := by
    funext N
    simp only [Nat.cast_add,Nat.cast_one,one_div,mul_inv_rev]
    ring
  rw [he]
  simpa only [mul_zero] using h

lemma sqrt_reciprocal_rank_tendsto_zero (K : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (1/(K*(N+1 : ℕ)))) atTop (𝓝 (0 : ℝ)) := by
  simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp (reciprocal_rank_tendsto_zero K)

end ProphetSecretary.Analysis
