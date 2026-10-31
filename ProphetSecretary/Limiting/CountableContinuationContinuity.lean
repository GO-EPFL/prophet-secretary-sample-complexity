import ProphetSecretary.Limiting.CountableContinuationApproximation
import ProphetSecretary.Limiting.CountableFiniteMask
import ProphetSecretary.Limiting.HybridHorizonContinuity
import ProphetSecretary.Analysis.ContinuousDiscreteParameter

/-!
# Joint continuity of actual countable remaining-state values

Finite mask projections and actual finite-hybrid horizon continuity give
continuous truncated functionals. Their proved uniform limit gives joint
continuity in the entire unseen mask and remaining horizon. This is a value
statement; optimality of a countable canonical policy is separate.
-/

open MeasureTheory Filter
open scoped Topology NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma continuous_finiteMask_continuation (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Continuous (fun z : (Fin N → Bool) × ℝ≥0 => (B.finiteMaskState N b hb z.1).continuationValue w c z.2) :=
  ProphetSecretary.Analysis.continuous_discrete_parameter
    (fun keep => (B.finiteMaskState N b hb keep).continuationValue w c)
    (fun keep => (B.finiteMaskState N b hb keep).continuous_continuationValue hw hc)

lemma continuous_truncatedContinuationValue (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Continuous (fun z : IndividualMask × ℝ≥0 => B.truncatedContinuationValue N b hb z.1 w c z.2) := by
  have h := (B.continuous_finiteMask_continuation N b hb hw hc).comp
    (((continuous_restrictIndividualMask N).comp continuous_fst).prodMk continuous_snd)
  have he : (fun z : IndividualMask × ℝ≥0 => B.truncatedContinuationValue N b hb z.1 w c z.2) =
      (fun z => (B.finiteMaskState N b hb (restrictIndividualMask N z.1)).continuationValue w c z.2) := by
    funext z
    exact congrArg (fun D : FiniteIntensityHybridInstance N => D.optimalScalarValue w (c*(z.2 : ℝ)))
      (B.remainingState_truncation_eq z.1 z.2 N b hb)
  rw [he]
  exact h

theorem continuous_continuationValue (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Continuous (fun z : IndividualMask × ℝ≥0 => B.continuationValue z.1 w c z.2) := by
  have h := B.truncatedContinuationValue_uniform_limit hw hc
  exact h.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall fun N =>
    B.continuous_truncatedContinuationValue N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw hc))

lemma measurable_continuationValue (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (fun z : IndividualMask × ℝ≥0 => B.continuationValue z.1 w c z.2) :=
  (B.continuous_continuationValue hw hc).measurable

end ProphetSecretary.Limiting.CountableInstance
