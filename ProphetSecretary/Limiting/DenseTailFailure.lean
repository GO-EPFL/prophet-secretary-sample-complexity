import ProphetSecretary.Limiting.ExtendedTailLevels
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Diverging actual tail counts make unconditional fallback failure vanish

Every finite tail count is finite before passing to the extended limit.
The real count and its exponential are derived from that actual finite data.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Limiting

lemma tailCount_tendsto_atTop_of_extended (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (ℓ : ℝ) (h : Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤)) :
    Tendsto (fun m => (P m).tailCount ℓ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  have hBound : ENNReal.ofReal (max R 0+1) < ⊤ := ENNReal.ofReal_lt_top
  filter_upwards [h.eventually (lt_mem_nhds hBound)] with m hm
  have hReal := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity : 0 ≤ max R 0+1)
    (extendedTailCount_finite (P m) ℓ).ne).mp hm
  rw [extendedTailCount_toReal] at hReal
  exact (by linarith only [hReal,le_max_left R 0])

lemma exp_neg_tailCount_tendsto_zero (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (ℓ : ℝ) (h : Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun m => Real.exp (-η*(P m).tailCount ℓ)) atTop (𝓝 (0 : ℝ)) := by
  have hTail := tailCount_tendsto_atTop_of_extended sizes P ℓ h
  have hScaled := hTail.const_mul_atTop hη
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hScaled
  simpa only [Function.comp_def,neg_mul] using he

end ProphetSecretary.Limiting
