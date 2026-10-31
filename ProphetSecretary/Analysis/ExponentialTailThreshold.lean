import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The logarithmic threshold in the first-moment proof

Above log(K(1+S)/a), the exponential prophet bound contributes at most half
the per-value canonical selection bound. Constants are left explicit.
-/

namespace ProphetSecretary.Analysis

lemma exponential_tail_threshold {C κ K S a L : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hK : 0 < K) (hS : 0 ≤ S) (ha : 0 < a)
    (hKκ : 2 * C * Real.exp 1 / κ ≤ K)
    (hL : Real.log (K * (1 + S) / a) ≤ L) :
    C * Real.exp (1 - L) ≤ κ * a / (2 * (1 + S)) := by
  have hd : 0 < 1 + S := by linarith
  have hR : 0 < K * (1 + S) / a := div_pos (mul_pos hK hd) ha
  have hexp := Real.exp_le_exp.mpr (sub_le_sub_left hL 1)
  have hbound := mul_le_mul_of_nonneg_left hexp hC
  have hexact : Real.exp (1 - Real.log (K * (1 + S) / a)) = Real.exp 1 / (K * (1 + S) / a) := by
    rw [Real.exp_sub, Real.exp_log hR]
  rw [hexact] at hbound
  have hprod := (div_le_iff₀ hκ).mp hKκ
  have hr : C * (Real.exp 1 / (K * (1 + S) / a)) ≤ κ * a / (2 * (1 + S)) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hR).mpr
    have heq : κ * a / (2 * (1 + S)) * (K * (1 + S) / a) = K * κ / 2 := by
      field_simp
    rw [heq]
    linarith only [hprod]
  exact hbound.trans hr

end ProphetSecretary.Analysis
