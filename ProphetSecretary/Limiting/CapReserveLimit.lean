import ProphetSecretary.Limiting.DenseTerminalLimits
import ProphetSecretary.Limiting.CountableCapReserve
import ProphetSecretary.Model.TerminalBenchmarkBounds

/-!
# The dense-supply limit at a positive cap reserve

The level and terminal window are fixed before the original finite-sequence
limit. The resulting convergence is uniform for bounded reward and duration
weights. The zero-cap endpoint is handled separately by exact cap identities.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting

lemma cap_reserve_convergence_of_dense_tails (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (hReserve : B.terminal = B.cap) (hH : 0 < B.cap) (W C : ℝ≥0)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (hBelow : ∀ ℓ, 0 ≤ ℓ → ℓ < (B.cap : ℝ) →
      Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
        |Model.optimalScalarValue (P m) w c-B.optimalScalarValue w c| < ε) ∧
      |(P m).expectedMaximum-B.expectedMaximum| < ε := by
  intro ε hε
  let δ := min ((B.cap : ℝ)/2) (ε/(16*((W : ℝ)+1)))
  let ℓ := (B.cap : ℝ)-δ
  let η := min (1/2 : ℝ) (ε/(16*((C : ℝ)+1)))
  have hδ : 0 < δ := lt_min (by exact_mod_cast (div_pos hH (by norm_num : (0 : ℝ≥0) < 2))) (div_pos hε (by positivity))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδH : δ ≤ (B.cap : ℝ)/2 := min_le_left _ _
  have hℓ0 : 0 ≤ ℓ := by dsimp only [ℓ]; linarith only [hδH,B.cap.property]
  have hℓH : ℓ < (B.cap : ℝ) := by dsimp only [ℓ]; linarith only [hδ]
  have hTail := hBelow ℓ hℓ0 hℓH
  have hL (m : ℕ) : (P m).tailCount B.cap ≤ 0 := by
    have he := extendedTailCount_eq_zero_above_cap (P m) (hcap m) (le_refl (B.cap : ℝ))
    have hr := congrArg ENNReal.toReal he
    simpa only [extendedTailCount_toReal,ENNReal.toReal_zero] using hr.le
  have hδBudget : δ*(16*((W : ℝ)+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 16*((W : ℝ)+1))).mp (min_le_right _ _)
  have hηBudget : η*(16*((C : ℝ)+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 16*((C : ℝ)+1))).mp (min_le_right _ _)
  have hWδ0 : 0 ≤ (W : ℝ)*δ := mul_nonneg W.property hδ.le
  have hCη0 : 0 ≤ (C : ℝ)*η := mul_nonneg C.property hη.le
  have hWδ : (W : ℝ)*δ ≤ ε/16 := by nlinarith only [hδBudget,hδ,hWδ0]
  have hδSmall : δ ≤ ε/16 := by nlinarith only [hδBudget,hWδ0]
  have hCη : (C : ℝ)*η ≤ ε/16 := by nlinarith only [hηBudget,hη,hCη0]
  have hWidth : (B.cap : ℝ)-ℓ = δ := by dsimp only [ℓ]; ring
  have hε4 : 0 < ε/4 := by positivity
  have hV := dense_terminal_scalar_eventual_error sizes P B.cap B.cap W C le_rfl hcap
    hℓ0 hℓH.le hη hη1 hTail hL (ε/4) hε4
  have hM := dense_terminal_benchmark_eventual_error sizes P B.cap B.cap le_rfl hcap
    hℓ0 hℓH.le hTail (ε/4) hε4
  filter_upwards [hV,hM] with m hmV hmM
  constructor
  · intro w c hw hwW hc hcC
    have hGap := hmV w c hw hwW hc hcC
    have hTerm : Model.optimalTerminalScalarValue (P m) B.cap w c = B.optimalScalarValue w c :=
      ((P m).optimalTerminalScalarValue_at_cap B.cap (hcap m) hw hc).trans (B.value_eq_cap_of_terminal hReserve hw hc).symm
    have hMain : (W : ℝ)*((B.cap : ℝ)-ℓ+(B.cap : ℝ)*η*0)+(C : ℝ)*η+ε/4 < ε := by
      rw [mul_zero,add_zero,hWidth]
      linarith only [hWδ,hCη,hε]
    rw [← hTerm,abs_sub_comm,abs_of_nonneg hGap.1]
    exact hGap.2.trans_lt hMain
  · have hTerm : (P m).expectedTerminalMaximum B.cap = B.expectedMaximum :=
      ((P m).expectedTerminalMaximum_at_cap B.cap (hcap m)).trans (B.expectedMaximum_eq_cap_of_terminal hReserve).symm
    rw [← hTerm,abs_sub_comm,abs_of_nonneg hmM.1]
    have hMain : (B.cap : ℝ)-ℓ+ε/4 < ε := by rw [hWidth]; linarith only [hδSmall,hε]
    exact hmM.2.trans hMain

end ProphetSecretary.Limiting
