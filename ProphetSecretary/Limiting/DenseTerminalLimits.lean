import ProphetSecretary.Limiting.DenseTailFailure
import ProphetSecretary.Limiting.DenseTerminalBenchmark
import ProphetSecretary.Model.DenseTerminalComparison
import ProphetSecretary.Model.TerminalZeroWeight

/-!
# Finite dense-supply terminal errors after the original-sequence limit

The reserve level and terminal window are fixed before this limit. Uniformity
in reward and duration weights is explicit, with the duration bound C retained.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting

lemma dense_terminal_scalar_eventual_error (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (H b W C : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    {ℓ η L : ℝ} (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b) (hη : 0 < η) (hη1 : η ≤ 1)
    (hTail : Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤))
    (hL : ∀ m, (P m).tailCount b ≤ L) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
      0 ≤ Model.optimalTerminalScalarValue (P m) b w c-Model.optimalScalarValue (P m) w c ∧
      Model.optimalTerminalScalarValue (P m) b w c-Model.optimalScalarValue (P m) w c ≤
        (W : ℝ)*((b : ℝ)-ℓ+(H : ℝ)*η*L)+(C : ℝ)*η+ε := by
  have hFailure : Tendsto (fun m => (W : ℝ)*(H : ℝ)*Real.exp (-η*(P m).tailCount ℓ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (exp_neg_tailCount_tendsto_zero sizes P ℓ hTail hη).const_mul ((W : ℝ)*(H : ℝ))
  intro ε hε
  filter_upwards [(tendsto_order.mp hFailure).2 ε hε] with m hm
  intro w c hw hwW hc hcC
  have hP := (P m).integrable_maximum_of_bounded (hcap m)
  have hWidth : 0 ≤ (b : ℝ)-ℓ := sub_nonneg.mpr hℓb
  by_cases hw0 : w = 0
  · subst w
    rw [Model.optimalTerminalScalarValue_zero_rewardWeight _ _ hc,
      Model.optimalScalarValue_zero_rewardWeight _ hc,sub_self]
    have hL0 : 0 ≤ L := by
      have ht : 0 ≤ (P m).tailCount b := by unfold Model.Instance.tailCount; positivity
      exact ht.trans (hL m)
    constructor
    · exact le_rfl
    · positivity
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have h := (P m).dense_terminal_value_comparison hP hη.le hη1 hℓ hℓb
    (show (b : ℝ) ≤ H by exact_mod_cast hbH) (hcap m) hwP hc
  have ht0 : 0 ≤ (P m).tailCount b := by unfold Model.Instance.tailCount; positivity
  have hBracket : 0 ≤ (b : ℝ)-ℓ+(H : ℝ)*η*(P m).tailCount b+
      (H : ℝ)*Real.exp (-η*(P m).tailCount ℓ) := by positivity
  have hWeight := mul_le_mul_of_nonneg_right hwW hBracket
  have hCount := mul_le_mul_of_nonneg_left (hL m) (mul_nonneg H.property hη.le)
  have hDuration := mul_le_mul_of_nonneg_right hcC hη.le
  have hMain := mul_le_mul_of_nonneg_left
    (add_le_add (show (b : ℝ)-ℓ ≤ (b : ℝ)-ℓ from le_rfl) hCount) W.property
  have hError : w*((b : ℝ)-ℓ+(H : ℝ)*η*(P m).tailCount b+
        (H : ℝ)*Real.exp (-η*(P m).tailCount ℓ))+c*η <
      (W : ℝ)*((b : ℝ)-ℓ+(H : ℝ)*η*L)+(C : ℝ)*η+ε := by
    calc
      _ ≤ (W : ℝ)*((b : ℝ)-ℓ+(H : ℝ)*η*(P m).tailCount b+
          (H : ℝ)*Real.exp (-η*(P m).tailCount ℓ))+(C : ℝ)*η := add_le_add hWeight hDuration
      _ = (W : ℝ)*((b : ℝ)-ℓ+(H : ℝ)*η*(P m).tailCount b)+(C : ℝ)*η+
          (W : ℝ)*(H : ℝ)*Real.exp (-η*(P m).tailCount ℓ) := by ring
      _ ≤ (W : ℝ)*((b : ℝ)-ℓ+(H : ℝ)*η*L)+(C : ℝ)*η+
          (W : ℝ)*(H : ℝ)*Real.exp (-η*(P m).tailCount ℓ) := add_le_add (add_le_add hMain le_rfl) le_rfl
      _ < _ := add_lt_add_of_le_of_lt le_rfl hm
  exact ⟨sub_nonneg.mpr h.2,(sub_le_comm.mp h.1).trans hError.le⟩

lemma dense_terminal_benchmark_eventual_error (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b)
    (hTail : Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop,
      0 ≤ (P m).expectedTerminalMaximum b-(P m).expectedMaximum ∧
      (P m).expectedTerminalMaximum b-(P m).expectedMaximum < (b : ℝ)-ℓ+ε := by
  have hFailure : Tendsto (fun m => (H : ℝ)*Real.exp (-(P m).tailCount ℓ)) atTop (𝓝 (0 : ℝ)) := by
    have h := (exp_neg_tailCount_tendsto_zero sizes P ℓ hTail (show (0 : ℝ) < 1 by norm_num)).const_mul (H : ℝ)
    simpa only [neg_one_mul,mul_zero] using h
  intro ε hε
  filter_upwards [(tendsto_order.mp hFailure).2 ε hε] with m hm
  have h := dense_terminal_benchmark_comparison (P m) ((P m).integrable_maximum_of_bounded (hcap m))
    hℓ hℓb (show (b : ℝ) ≤ H by exact_mod_cast hbH)
  exact ⟨h.1,by linarith only [h.2,hm]⟩

end ProphetSecretary.Limiting
