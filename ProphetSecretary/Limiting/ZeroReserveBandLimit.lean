import ProphetSecretary.Limiting.CountablePrefixUniform
import ProphetSecretary.Model.TerminalValueComparison
import ProphetSecretary.Model.TerminalBenchmarkBounds

/-!
# Removing the cutoff when the terminal reserve is zero

This comparison takes the original-sequence limit before increasing the
retained prefix, then chooses a common continuity cutoff near zero. It uses
actual full-policy finite and countable scalar values and actual maxima.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting

lemma zero_reserve_convergence_of_band_limits (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (hZero : B.terminal = 0) (W : ℝ≥0)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (good : ℝ≥0 → Prop)
    (hGood : ∀ δ > (0 : ℝ), ∃ b : ℝ≥0, 0 < b ∧ b ≤ B.cap ∧ (b : ℝ) < δ ∧ good b)
    (hBands : ∀ (b : ℝ≥0) (hb : (B.terminal : ℝ) < b) (hbH : b ≤ B.cap), good b →
      (∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop, ∀ w c : ℝ,
        0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
        |Model.optimalTerminalScalarValue (P m) b w c-
          (B.prefixIntensityState N b hbH (B.intensityAbove b hb)
            (B.truncation N b hb).intensity_supported).optimalScalarValue w c| < ε) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop,
        |(P m).expectedTerminalMaximum b-
          (B.prefixIntensityState N b hbH (B.intensityAbove b hb)
            (B.truncation N b hb).intensity_supported).expectedMaximum| < ε)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
        |Model.optimalScalarValue (P m) w c-B.optimalScalarValue w c| < ε) ∧
      |(P m).expectedMaximum-B.expectedMaximum| < ε := by
  intro ε hε
  have hε4 : 0 < ε/4 := by positivity
  let δV := (ε/4)/(4*((W : ℝ)+1))
  have hδV : 0 < δV := div_pos hε4 (by positivity)
  obtain ⟨NV,hNearV⟩ := B.prefixIntensityState_value_uniform W.property hε4
  obtain ⟨NM,δM,hδM,hNearM⟩ := B.prefixIntensityState_benchmark_uniform hε4
  obtain ⟨b,hb0,hbH,hbSmall,hbGood⟩ := hGood (min δM (min δV (ε/4)))
    (lt_min hδM (lt_min hδV hε4))
  have hb : (B.terminal : ℝ) < b := by
    rw [hZero]
    exact_mod_cast hb0
  have hbM : (b : ℝ) < δM := hbSmall.trans_le (min_le_left _ _)
  have hbV : (b : ℝ) < δV := (hbSmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hbε : (b : ℝ) < ε/4 := (hbSmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hWb : (W : ℝ)*(b : ℝ) < ε/4 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4*((W : ℝ)+1))).mp hbV
    have hp := mul_nonneg W.property b.property
    nlinarith only [h,hp,b.property,hε]
  have hbV' : (b : ℝ) < (B.terminal : ℝ)+δV := by simpa only [hZero,NNReal.coe_zero,zero_add] using hbV
  have hbM' : (b : ℝ) < (B.terminal : ℝ)+δM := by simpa only [hZero,NNReal.coe_zero,zero_add] using hbM
  have hBand := hBands b hb hbH hbGood
  have hNs := ((hBand.1 (ε/4) hε4).and (hBand.2 (ε/4) hε4)).and
    (eventually_ge_atTop (max NV NM))
  obtain ⟨N,⟨hNS,hNM⟩,hN⟩ := hNs.exists
  let D := B.prefixIntensityState N b hbH (B.intensityAbove b hb) (B.truncation N b hb).intensity_supported
  have hNV : NV ≤ N := (le_max_left _ _).trans hN
  have hNM' : NM ≤ N := (le_max_right _ _).trans hN
  have hModelM := hNearM N hNM' b hb hbH hbM'
  change |D.expectedMaximum-B.expectedMaximum| < ε/4 at hModelM
  filter_upwards [hNS,hNM] with m hmS hmM
  have hP := (P m).integrable_maximum_of_bounded (hcap m)
  constructor
  · intro w c hw hwW hc
    have hOrd := (P m).terminal_value_comparison_nonnegative hP b.property hw hc
    have hGap : |Model.optimalScalarValue (P m) w c-Model.optimalTerminalScalarValue (P m) b w c| ≤ w*(b : ℝ) := by
      calc
        _ = |Model.optimalTerminalScalarValue (P m) b w c-Model.optimalScalarValue (P m) w c| := abs_sub_comm _ _
        _ = Model.optimalTerminalScalarValue (P m) b w c-Model.optimalScalarValue (P m) w c :=
          abs_of_nonneg (sub_nonneg.mpr hOrd.1)
        _ ≤ _ := sub_le_iff_le_add'.mpr hOrd.2
    have hGap' := hGap.trans (mul_le_mul_of_nonneg_right hwW b.property)
    have hFinite := hmS w c hw hwW hc
    change |Model.optimalTerminalScalarValue (P m) b w c-D.optimalScalarValue w c| < ε/4 at hFinite
    have hModel := hNearV N hNV b hb hbH hbV' w c hw hwW hc
    change |D.optimalScalarValue w c-B.optimalScalarValue w c| < ε/4 at hModel
    calc
      _ ≤ |Model.optimalScalarValue (P m) w c-Model.optimalTerminalScalarValue (P m) b w c|+
          |Model.optimalTerminalScalarValue (P m) b w c-B.optimalScalarValue w c| := abs_sub_le _ _ _
      _ ≤ |Model.optimalScalarValue (P m) w c-Model.optimalTerminalScalarValue (P m) b w c|+
          (|Model.optimalTerminalScalarValue (P m) b w c-D.optimalScalarValue w c|+
            |D.optimalScalarValue w c-B.optimalScalarValue w c|) := add_le_add le_rfl (abs_sub_le _ _ _)
      _ < ε := by linarith only [hGap',hWb,hFinite,hModel,hε]
  · have hOrd := (P m).terminal_benchmark_comparison hP b.property
    have hGap : |(P m).expectedMaximum-(P m).expectedTerminalMaximum b| ≤ (b : ℝ) := by
      calc
        _ = |(P m).expectedTerminalMaximum b-(P m).expectedMaximum| := abs_sub_comm _ _
        _ = (P m).expectedTerminalMaximum b-(P m).expectedMaximum := abs_of_nonneg hOrd.1
        _ ≤ _ := hOrd.2
    change |(P m).expectedTerminalMaximum b-D.expectedMaximum| < ε/4 at hmM
    calc
      _ ≤ |(P m).expectedMaximum-(P m).expectedTerminalMaximum b|+
          |(P m).expectedTerminalMaximum b-B.expectedMaximum| := abs_sub_le _ _ _
      _ ≤ |(P m).expectedMaximum-(P m).expectedTerminalMaximum b|+
          (|(P m).expectedTerminalMaximum b-D.expectedMaximum|+|D.expectedMaximum-B.expectedMaximum|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ < ε := by linarith only [hGap,hbε,hmM,hModelM,hε]

end ProphetSecretary.Limiting
