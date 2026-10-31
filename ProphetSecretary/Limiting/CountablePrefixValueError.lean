import ProphetSecretary.Limiting.CountablePrefixState
import ProphetSecretary.Limiting.CountableValueLimit
import ProphetSecretary.Limiting.HybridTerminalComparison

/-!
# Prefix-state error with cutoff and terminal reward moved together

The finite-prefix state has terminal b, while the full model has reserve a.
Its value error is controlled by the actual omitted individual maximum and
2(b−a), uniformly over every nonnegative duration weight.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Limiting.CountableInstance

theorem prefixIntensityState_value_error_le (B : CountableInstance) (N : ℕ) (b : ℝ≥0)
    (hb : (B.terminal : ℝ) < b) (hbH : b ≤ B.cap) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |(B.prefixIntensityState N b hbH (B.intensityAbove b hb)
        (B.truncation N b hb).intensity_supported).optimalScalarValue w c-B.optimalScalarValue w c| ≤
      w*(B.expectedIndividualTailExcessMaximum N+2*((b : ℝ)-B.terminal)) := by
  let C := B.truncation N b hb
  let D := B.prefixIntensityState N b hbH (B.intensityAbove b hb) C.intensity_supported
  have hTerminal := C.value_terminal_abs_sub_le D rfl rfl hw c
  have hTerminal' : |D.optimalScalarValue w c-C.optimalScalarValue w c| ≤
      w*((b : ℝ)-B.terminal) := by
    rw [abs_sub_comm]
    have he : |(C.terminal : ℝ)-D.terminal| = (b : ℝ)-B.terminal := by
      change |(B.terminal : ℝ)-(b : ℝ)| = _
      rw [abs_of_neg (sub_neg.mpr hb),neg_sub]
    rwa [he] at hTerminal
  have hTrunc := B.truncation_value_error_le N hb hw hc
  change |D.optimalScalarValue w c-B.optimalScalarValue w c| ≤ _
  calc
    _ ≤ |D.optimalScalarValue w c-C.optimalScalarValue w c|+
        |C.optimalScalarValue w c-B.optimalScalarValue w c| := abs_sub_le _ _ _
    _ ≤ w*((b : ℝ)-B.terminal)+w*(B.expectedIndividualTailExcessMaximum N+((b : ℝ)-B.terminal)) :=
      add_le_add hTerminal' hTrunc
    _ = _ := by ring

end ProphetSecretary.Limiting.CountableInstance
