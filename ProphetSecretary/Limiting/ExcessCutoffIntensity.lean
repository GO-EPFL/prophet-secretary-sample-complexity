import ProphetSecretary.Limiting.HybridReserveShift
import ProphetSecretary.Limiting.CausalPoissonReserve

/-!
# Anonymous marks at most the terminal reward

Deleting these marks preserves the actual all-policy scalar value. The proof
uses exact reserve removal: their excess pushforward contributes only zero,
which is excluded from the positive excess intensity.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

lemma excessIntensity_restrict_reserve (μ : FiniteMeasure ℝ) {a : ℝ} (ha : 0 ≤ a) :
    excessIntensity (μ.restrict (Ioi a)) a = excessIntensity μ a := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  change ((((μ : Measure ℝ).restrict (Ioi a)).map (Model.excessValueMap a)).restrict (Ioi 0)) E =
    (((μ : Measure ℝ).map (Model.excessValueMap a)).restrict (Ioi 0)) E
  rw [Measure.restrict_apply hE,Measure.restrict_apply hE,
    Measure.map_apply (Model.measurable_excessValueMap a) (hE.inter measurableSet_Ioi),
    Measure.map_apply (Model.measurable_excessValueMap a) (hE.inter measurableSet_Ioi),
    Measure.restrict_apply ((Model.measurable_excessValueMap a) (hE.inter measurableSet_Ioi))]
  congr 1
  apply inter_eq_left.mpr
  intro x hx
  exact (Model.excessValueMap_positive_iff ha).mp hx.2

variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.cutoffAtTerminal (B : FiniteIntensityHybridInstance n) :
    FiniteIntensityHybridInstance n :=
  { B with
    intensity := B.intensity.restrict (Ioi (B.terminal : ℝ))
    intensity_supported := ae_restrict_of_ae B.intensity_supported }

lemma FiniteIntensityHybridInstance.cutoffAtTerminal_excess (B : FiniteIntensityHybridInstance n) :
    B.cutoffAtTerminal.excessState B.terminal = B.excessState B.terminal := by
  apply FiniteIntensityHybridInstance.ext_data
  · rfl
  · rfl
  · rfl
  · exact excessIntensity_restrict_reserve B.intensity B.terminal.property

theorem FiniteIntensityHybridInstance.value_cutoffAtTerminal (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.cutoffAtTerminal.optimalScalarValue w c = B.optimalScalarValue w c := by
  by_cases hw0 : w = 0
  · subst w
    rw [B.cutoffAtTerminal.value_zero_rewardWeight hc,B.value_zero_rewardWeight hc]
  · have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    rw [B.cutoffAtTerminal.value_reserveShift hwP hc,B.value_reserveShift hwP hc]
    change w*(B.terminal : ℝ)+(B.cutoffAtTerminal.excessState B.terminal).optimalScalarValue w c = _
    rw [B.cutoffAtTerminal_excess]

end ProphetSecretary.Limiting
