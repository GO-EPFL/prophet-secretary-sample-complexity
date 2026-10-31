import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Symmetric logarithmic divergence

The scalar inequality used to bound the second moment of the posterior sign in
`thm:bayes`: `(r-1) log r ≥ 2(r-1)²/(r+1)` for positive likelihood ratios.
-/

namespace ProphetSecretary.Analysis

theorem symmetricLog_ge_triangular {r : ℝ} (hr : 0 < r) :
    2 * (r - 1) ^ 2 / (r + 1) ≤ (r - 1) * Real.log r := by
  have hlarge (s : ℝ) (hs : 1 ≤ s) :
      2 * (s - 1) ^ 2 / (s + 1) ≤ (s - 1) * Real.log s := by
    have h := Real.le_log_one_add_of_nonneg (sub_nonneg.mpr hs)
    have heq₁ : 1 + (s - 1) = s := by ring
    have heq₂ : s - 1 + 2 = s + 1 := by ring
    rw [heq₁, heq₂] at h
    have hm := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs)
    have heq : 2 * (s - 1) ^ 2 / (s + 1) = (s - 1) * (2 * (s - 1) / (s + 1)) := by ring
    rw [heq]
    exact hm
  by_cases hr1 : 1 ≤ r
  · exact hlarge r hr1
  · have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr (not_le.mp hr1).le
    have h := mul_le_mul_of_nonneg_left (hlarge r⁻¹ hinv) hr.le
    have heq₁ : r * (2 * (r⁻¹ - 1) ^ 2 / (r⁻¹ + 1)) = 2 * (r - 1) ^ 2 / (r + 1) := by
      field_simp
      ring
    have heq₂ : r * ((r⁻¹ - 1) * Real.log r⁻¹) = (r - 1) * Real.log r := by
      rw [Real.log_inv]
      field_simp
      ring
    rwa [heq₁, heq₂] at h

end ProphetSecretary.Analysis
