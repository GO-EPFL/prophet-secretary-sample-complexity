import ProphetSecretary.Limiting.CountableContinuationApproximation
import ProphetSecretary.Limiting.CountableFiniteMask

/-!
# Remaining-horizon monotonicity of actual countable scalar values

The horizon is remaining time, so the value is increasing in this parameter.
The proof passes the genuine finite-hybrid horizon inequalities through the
proved full-model uniform approximation.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Limiting.CountableInstance

theorem continuationValue_mono (B : CountableInstance) (keep : IndividualMask)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : Monotone (B.continuationValue keep w c) := by
  intro u v huv
  have hUniform := B.truncatedContinuationValue_uniform_limit hw hc
  have hU := hUniform.tendsto_at (keep,u)
  have hV := hUniform.tendsto_at (keep,v)
  apply le_of_tendsto_of_tendsto hU hV
  filter_upwards [] with N
  let D := B.finiteMaskState N (B.markCutoff N) (B.terminal_lt_markCutoff N) (restrictIndividualMask N keep)
  have hLeft := congrArg (fun C : FiniteIntensityHybridInstance N => C.optimalScalarValue w (c*(u : ℝ)))
    (B.remainingState_truncation_eq keep u N (B.markCutoff N) (B.terminal_lt_markCutoff N))
  have hRight := congrArg (fun C : FiniteIntensityHybridInstance N => C.optimalScalarValue w (c*(v : ℝ)))
    (B.remainingState_truncation_eq keep v N (B.markCutoff N) (B.terminal_lt_markCutoff N))
  exact hLeft.le.trans ((D.continuationValue_mono hw hc huv).trans hRight.symm.le)

end ProphetSecretary.Limiting.CountableInstance
