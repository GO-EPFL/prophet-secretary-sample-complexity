import ProphetSecretary.Limiting.CountableValueLimit
import ProphetSecretary.Limiting.HybridIntensityComparison

/-!
# Intensity monotonicity for the full countable policy value

For common retained laws, reserve and cap, the finite-hybrid intensity
comparison passes through the proved actual full-policy truncation limits.
Thus the comparison concerns every admissible randomized stopping policy,
without assuming a policy-thinning interface or optimizer convergence.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance

theorem optimalScalarValue_mono_intensity (B D : CountableInstance)
    (hCap : D.cap=B.cap) (hTerm : D.terminal=B.terminal)
    (hP : D.individuals=B.individuals) (hIntensity : B.intensity≤D.intensity)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c ≤ D.optimalScalarValue w c := by
  have hDcut (m : ℕ) : (D.terminal : ℝ)<B.markCutoff m := by
    rw [hTerm]
    exact B.terminal_lt_markCutoff m
  have hDlimit : Tendsto B.markCutoff atTop (𝓝 (D.terminal : ℝ)) := by rw [hTerm]; exact B.markCutoff_tendsto
  have hB := B.truncation_value_tendsto (fun m : ℕ => m) B.markCutoff
    B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hc
  have hD := D.truncation_value_tendsto (fun m : ℕ => m) B.markCutoff hDcut tendsto_id hDlimit hw hc
  apply le_of_tendsto_of_tendsto hB hD
  filter_upwards [] with m
  have hPrefix : D.individualPrefix m=B.individualPrefix m := by
    apply Model.Instance.eq_of_law_eq
    funext i
    change (D.individuals i.val : Measure ℝ)=(B.individuals i.val : Measure ℝ)
    rw [hP]
  apply FiniteIntensityHybridInstance.optimalScalarValue_mono_intensity
    (B.truncation m (B.markCutoff m) (B.terminal_lt_markCutoff m))
    (D.truncation m (B.markCutoff m) (hDcut m))
  · exact hCap.le
  · exact hTerm
  · exact hPrefix
  · exact Measure.restrict_mono_measure hIntensity _
  · exact hw
  · exact hc

end ProphetSecretary.Limiting.CountableInstance
