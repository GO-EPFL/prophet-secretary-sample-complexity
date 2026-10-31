import ProphetSecretary.Limiting.CountablePrefixUniform
import ProphetSecretary.Limiting.DenseTerminalLimits

/-!
# Removing a positive reserve cutoff using actual dense finite supply

The cutoff, fallback level and final window are chosen before the original
sequence index. The retained prefix is chosen after the cutoff. Every error is
uniform on the displayed bounded weight rectangle and independent of size.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting

lemma positive_reserve_convergence_of_band_limits (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (hA : 0 < B.terminal) (W C : ℝ≥0)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (good : ℝ≥0 → Prop)
    (hGood : ∀ δ > (0 : ℝ), ∃ b : ℝ≥0, (B.terminal : ℝ) < b ∧ b ≤ B.cap ∧
      (b : ℝ) < (B.terminal : ℝ)+δ ∧ good b)
    (L : ℝ≥0 → ℝ≥0)
    (hAbove : ∀ (b : ℝ≥0) (_hb : (B.terminal : ℝ) < b) (_hbH : b ≤ B.cap), good b →
      ∀ m, (P m).tailCount b ≤ (L b : ℝ))
    (hBelow : ∀ ℓ, 0 ≤ ℓ → ℓ < (B.terminal : ℝ) →
      Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤))
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
      (∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
        |Model.optimalScalarValue (P m) w c-B.optimalScalarValue w c| < ε) ∧
      |(P m).expectedMaximum-B.expectedMaximum| < ε := by
  intro ε hε
  have hε4 : 0 < ε/4 := by positivity
  have hε16 : 0 < ε/16 := by positivity
  let δV := (ε/4)/(4*((W : ℝ)+1))
  have hδV : 0 < δV := div_pos hε4 (by positivity)
  obtain ⟨NV,hNearV⟩ := B.prefixIntensityState_value_uniform W.property hε4
  obtain ⟨NM,δM,hδM,hNearM⟩ := B.prefixIntensityState_benchmark_uniform hε4
  obtain ⟨b,hb,hbH,hbSmall,hbGood⟩ := hGood (min δM δV) (lt_min hδM hδV)
  let d := (b : ℝ)-(B.terminal : ℝ)
  have hd : 0 < d := sub_pos.mpr hb
  have hbM : (b : ℝ) < (B.terminal : ℝ)+δM := hbSmall.trans_le (add_le_add le_rfl (min_le_left _ _))
  have hbV : (b : ℝ) < (B.terminal : ℝ)+δV := hbSmall.trans_le (add_le_add le_rfl (min_le_right _ _))
  have hdV : d < δV := by dsimp only [d]; linarith only [hbV]
  have hdb := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4*((W : ℝ)+1))).mp hdV
  have hWd0 : 0 ≤ (W : ℝ)*d := mul_nonneg W.property hd.le
  have hWd : (W : ℝ)*d < ε/16 := by nlinarith only [hdb,hd,hWd0]
  have hdSmall : d < ε/16 := by nlinarith only [hdb,hWd0]
  let δ := min ((B.terminal : ℝ)/2) (ε/(64*((W : ℝ)+1)))
  let ℓ := (B.terminal : ℝ)-δ
  have hA' : (0 : ℝ) < B.terminal := by exact_mod_cast hA
  have hδ : 0 < δ := lt_min (div_pos hA' (by norm_num)) (div_pos hε (by positivity))
  have hδA : δ ≤ (B.terminal : ℝ)/2 := min_le_left _ _
  have hℓ0 : 0 ≤ ℓ := by dsimp only [ℓ]; linarith only [hδA,B.terminal.property]
  have hℓA : ℓ < (B.terminal : ℝ) := by dsimp only [ℓ]; linarith only [hδ]
  have hℓb : ℓ ≤ b := hℓA.le.trans hb.le
  have hδBudget : δ*(64*((W : ℝ)+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 64*((W : ℝ)+1))).mp (min_le_right _ _)
  have hWδ0 : 0 ≤ (W : ℝ)*δ := mul_nonneg W.property hδ.le
  have hWδ : (W : ℝ)*δ ≤ ε/64 := by nlinarith only [hδBudget,hδ,hWδ0]
  have hδSmall : δ ≤ ε/64 := by nlinarith only [hδBudget,hWδ0]
  let K : ℝ := (W : ℝ)*(B.cap : ℝ)*(L b : ℝ)+(C : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let η := min (1/2 : ℝ) (ε/(64*(K+1)))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hηBudget : η*(64*(K+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 64*(K+1))).mp (min_le_right _ _)
  have hKη0 : 0 ≤ K*η := mul_nonneg hK hη.le
  have hKη : K*η ≤ ε/64 := by nlinarith only [hηBudget,hη,hKη0]
  have hWidth : (b : ℝ)-ℓ = d+δ := by dsimp only [d,ℓ]; ring
  have hMainS : (W : ℝ)*((b : ℝ)-ℓ+(B.cap : ℝ)*η*(L b : ℝ))+(C : ℝ)*η+ε/16 < ε/4 := by
    have he : (W : ℝ)*((b : ℝ)-ℓ+(B.cap : ℝ)*η*(L b : ℝ))+(C : ℝ)*η+ε/16 =
        (W : ℝ)*d+(W : ℝ)*δ+K*η+ε/16 := by rw [hWidth]; dsimp only [K]; ring
    rw [he]
    linarith only [hWd,hWδ,hKη,hε]
  have hMainM : (b : ℝ)-ℓ+ε/16 < ε/4 := by rw [hWidth]; linarith only [hdSmall,hδSmall,hε]
  have hTail := hBelow ℓ hℓ0 hℓA
  have hDenseS := dense_terminal_scalar_eventual_error sizes P B.cap b W C hbH hcap hℓ0 hℓb
    hη hη1 hTail (hAbove b hb hbH hbGood) (ε/16) hε16
  have hDenseM := dense_terminal_benchmark_eventual_error sizes P B.cap b hbH hcap hℓ0 hℓb hTail (ε/16) hε16
  have hBand := hBands b hb hbH hbGood
  have hNs := ((hBand.1 (ε/4) hε4).and (hBand.2 (ε/4) hε4)).and
    (eventually_ge_atTop (max NV NM))
  obtain ⟨N,⟨hNS,hNM⟩,hN⟩ := hNs.exists
  let D := B.prefixIntensityState N b hbH (B.intensityAbove b hb) (B.truncation N b hb).intensity_supported
  have hNV : NV ≤ N := (le_max_left _ _).trans hN
  have hNM' : NM ≤ N := (le_max_right _ _).trans hN
  have hModelM := hNearM N hNM' b hb hbH hbM
  change |D.expectedMaximum-B.expectedMaximum| < ε/4 at hModelM
  filter_upwards [hNS,hNM,hDenseS,hDenseM] with m hmS hmM hmDS hmDM
  constructor
  · intro w c hw hwW hc hcC
    have hDS := hmDS w c hw hwW hc hcC
    have hGap : |Model.optimalScalarValue (P m) w c-Model.optimalTerminalScalarValue (P m) b w c| < ε/4 := by
      calc
        _ = |Model.optimalTerminalScalarValue (P m) b w c-Model.optimalScalarValue (P m) w c| := abs_sub_comm _ _
        _ = Model.optimalTerminalScalarValue (P m) b w c-Model.optimalScalarValue (P m) w c := abs_of_nonneg hDS.1
        _ ≤ _ := hDS.2
        _ < ε/4 := hMainS
    have hFinite := hmS w c hw hwW hc
    change |Model.optimalTerminalScalarValue (P m) b w c-D.optimalScalarValue w c| < ε/4 at hFinite
    have hModel := hNearV N hNV b hb hbH hbV w c hw hwW hc
    change |D.optimalScalarValue w c-B.optimalScalarValue w c| < ε/4 at hModel
    calc
      _ ≤ |Model.optimalScalarValue (P m) w c-Model.optimalTerminalScalarValue (P m) b w c|+
          |Model.optimalTerminalScalarValue (P m) b w c-B.optimalScalarValue w c| := abs_sub_le _ _ _
      _ ≤ |Model.optimalScalarValue (P m) w c-Model.optimalTerminalScalarValue (P m) b w c|+
          (|Model.optimalTerminalScalarValue (P m) b w c-D.optimalScalarValue w c|+
            |D.optimalScalarValue w c-B.optimalScalarValue w c|) := add_le_add le_rfl (abs_sub_le _ _ _)
      _ < ε := by linarith only [hGap,hFinite,hModel,hε]
  · have hGap : |(P m).expectedMaximum-(P m).expectedTerminalMaximum b| < ε/4 := by
      calc
        _ = |(P m).expectedTerminalMaximum b-(P m).expectedMaximum| := abs_sub_comm _ _
        _ = (P m).expectedTerminalMaximum b-(P m).expectedMaximum := abs_of_nonneg hmDM.1
        _ < _ := hmDM.2
        _ < ε/4 := hMainM
    change |(P m).expectedTerminalMaximum b-D.expectedMaximum| < ε/4 at hmM
    calc
      _ ≤ |(P m).expectedMaximum-(P m).expectedTerminalMaximum b|+
          |(P m).expectedTerminalMaximum b-B.expectedMaximum| := abs_sub_le _ _ _
      _ ≤ |(P m).expectedMaximum-(P m).expectedTerminalMaximum b|+
          (|(P m).expectedTerminalMaximum b-D.expectedMaximum|+|D.expectedMaximum-B.expectedMaximum|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ < ε := by linarith only [hGap,hmM,hModelM,hε]

end ProphetSecretary.Limiting
