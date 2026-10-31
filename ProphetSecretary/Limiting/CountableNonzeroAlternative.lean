import ProphetSecretary.Limiting.CountablePrunedMeanBenchmark
import ProphetSecretary.Limiting.CountableMeanPrefixValueLower

/-!
# The zero-duration-response alternative is impossible at criticality

Only finite operations are applied to each pruned mean prefix. Their actual
benchmark preservation and explicit original-tail error force the finite
deterministic mean maxima to converge to the original prophet expectation.
The timed known-offer lower bound then contradicts criticality, because its
duration is strictly larger than the global competitive ratio. No optimizer
or score convergence is inferred from value convergence.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem meanPrefixMaximum_tendsto_of_zero_responses (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (hIndividual : B.AllIndividualDurationScoresZero w c) (hBand : B.AllPositiveBandDurationScoresZero w c) :
    Tendsto B.meanPrefixMaximum atTop (𝓝 B.expectedMaximum) := by
  have hTerminal := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hCutoff : Tendsto B.markCutoff atTop (𝓝 (0 : ℝ)) := by
    simpa only [hTerminal,NNReal.coe_zero] using B.markCutoff_tendsto
  have hError : Tendsto (fun N => B.expectedIndividualTailExcessMaximum N+B.markCutoff N) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using B.expectedIndividualTailExcessMaximum_tendsto.add hCutoff
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hError
  intro N
  have hBound := B.prunedMeanPrefix_expectedMaximum_le hTerminal N
  rw [(B.prunedMeanPrefix_preserves_criticality hw hc hCritical hIndividual hBand N).2.1] at hBound
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (B.meanPrefixMaximum_le_expectedMaximum N))]
  linarith only [hBound]

theorem not_all_duration_scores_zero_at_critical (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    ¬(B.AllIndividualDurationScoresZero w c ∧ B.AllPositiveBandDurationScoresZero w c) := by
  rintro ⟨hIndividual,hBand⟩
  have hMeans := B.meanPrefixMaximum_tendsto_of_zero_responses hw hc hCritical hIndividual hBand
  have hLower : w*optimalCompetitiveRatio*B.expectedMaximum+c*(1-optimalCompetitiveRatio^2/2) ≤
      B.optimalScalarValue w c := by
    apply le_of_tendsto_of_tendsto
      ((hMeans.const_mul (w*optimalCompetitiveRatio)).add_const (c*(1-optimalCompetitiveRatio^2/2))) tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact B.meanPrefix_knownOffer_lower hw hc hCritical hIndividual hBand N hN
  have hBase : B.optimalScalarValue w c=optimalCompetitiveRatio*(w*B.expectedMaximum+c) :=
    sub_eq_zero.mp hCritical.2
  have hStrict := mul_lt_mul_of_pos_left globalRatio_knownOffer_duration_strict hc
  nlinarith only [hLower,hBase,hStrict]

end ProphetSecretary.Limiting.CountableInstance
