import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Explicit uniform constants for normalized law curvature -/
namespace ProphetSecretary.Analysis

noncomputable def lawCurvatureConstant (H δ : ℝ) : ℝ := 8 * (H + 1) + 6 * H / δ

lemma lawCurvatureConstant_nonnegative {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) :
    0 ≤ lawCurvatureConstant H δ := by unfold lawCurvatureConstant; positivity

lemma lawCurvatureCoefficient_le {H δ w c S : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1) (hδc : δ ≤ c) (hS : 0 ≤ S) :
    8 * (w * H + c) + 6 * w ^ 2 * H * S / c ≤ lawCurvatureConstant H δ * (1 + S) := by
  have hwSq : w ^ 2 ≤ 1 := by nlinarith
  have hRatio : w ^ 2 / c ≤ 1 / δ := by
    apply (div_le_div_iff₀ hc hδ).2
    have ht := mul_le_mul_of_nonneg_right hwSq hδ.le
    nlinarith
  have hWeighted := mul_le_mul_of_nonneg_left hRatio (show 0 ≤ 6 * H * S by positivity)
  have hTerm : 6 * w ^ 2 * H * S / c ≤ (6 * H / δ) * S := by
    calc
      _ = 6 * H * S * (w ^ 2 / c) := by ring
      _ ≤ 6 * H * S * (1 / δ) := hWeighted
      _ = _ := by ring
  have hBase : 8 * (w * H + c) ≤ 8 * (H + 1) := by
    have := mul_le_mul_of_nonneg_right hw1 hH
    nlinarith
  apply (add_le_add hBase hTerm).trans
  unfold lawCurvatureConstant
  have hA : 0 ≤ 8 * (H + 1) * S := by positivity
  have hB : 0 ≤ 6 * H / δ := by positivity
  nlinarith


noncomputable def lawCoefficientRangeConstant (H W C δ : ℝ) : ℝ :=
  8 * (W * H + C) + 6 * W ^ 2 * H / δ

lemma lawCurvatureCoefficient_range_le {H W C δ w c S : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (hw : 0 ≤ w) (hwW : w ≤ W) (hc : 0 < c) (hcC : c ≤ C) (hδc : δ ≤ c) (hS : 0 ≤ S) :
    8 * (w * H + c) + 6 * w ^ 2 * H * S / c ≤ lawCoefficientRangeConstant H W C δ * (1 + S) := by
  have hW : 0 ≤ W := hw.trans hwW
  have hC : 0 ≤ C := hc.le.trans hcC
  have hwSq : w ^ 2 ≤ W ^ 2 := by nlinarith
  have hRatio : w ^ 2 / c ≤ W ^ 2 / δ := by
    apply (div_le_div_iff₀ hc hδ).2
    exact (mul_le_mul_of_nonneg_right hwSq hδ.le).trans (mul_le_mul_of_nonneg_left hδc (sq_nonneg W))
  have hWeighted := mul_le_mul_of_nonneg_left hRatio (show 0 ≤ 6 * H * S by positivity)
  have hTerm : 6 * w ^ 2 * H * S / c ≤ (6 * W ^ 2 * H / δ) * S := by
    calc
      _ = 6 * H * S * (w ^ 2 / c) := by ring
      _ ≤ 6 * H * S * (W ^ 2 / δ) := hWeighted
      _ = _ := by ring
  have hBase : 8 * (w * H + c) ≤ 8 * (W * H + C) := by
    have := mul_le_mul_of_nonneg_right hwW hH
    nlinarith
  apply (add_le_add hBase hTerm).trans
  unfold lawCoefficientRangeConstant
  have hA : 0 ≤ 8 * (W * H + C) * S := by positivity
  have hB : 0 ≤ 6 * W ^ 2 * H / δ := by positivity
  nlinarith

end ProphetSecretary.Analysis
