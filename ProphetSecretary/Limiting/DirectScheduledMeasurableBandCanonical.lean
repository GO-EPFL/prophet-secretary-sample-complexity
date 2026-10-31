import ProphetSecretary.Limiting.DirectScheduledMeasurableBandCoarse
import ProphetSecretary.Limiting.FiniteCanonicalScoreLimit
import ProphetSecretary.Limiting.CountableTruncationScoreLimit

/-!
# Actual canonical score limits for measurable positive bands

At each fixed coarse comparator the direct-schedule score covariances have
already converged. The common positive-tail profile and the complete-score
information bound control replacement by the actual finite optimizer. The
array limit precedes coarse refinement; the latter uses the full countable
outcome comparison for an arbitrary square-integrable analytical score.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem directScheduled_canonical_measurableBand_score_limits
    (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hNorm : w+c=1) :
    let π := fun m => (B.directFiniteApproximation hZero m).valuePolicy
      ((B.directFiniteApproximation hZero m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero m)) hw.le hc.le
    Tendsto (fun m => (π m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (π m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  let P := B.directFiniteApproximation hZero
  let sizes := fun m => m+B.directVirtualCount hZero m
  let D := fun j => B.truncation j (B.markCutoff j) (B.terminal_lt_markCutoff j)
  let πc := fun j => (D j).valueThresholdPolicy hw.le hc.le
  let γ := fun j m => directCoarsePolicy m (B.directVirtualCount hZero m) (πc j) (B.markCutoff j)
  let bR := fun j => ∫ v, B.bandScore S v*(B.truncatedValueRule j (B.markCutoff j)
    (B.terminal_lt_markCutoff j) w c).realizedReward B.terminal v ∂B.completeWorldLaw (Measure.dirac ())
  let bT := fun j => ∫ v, B.bandScore S v*(B.truncatedValueRule j (B.markCutoff j)
    (B.terminal_lt_markCutoff j) w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())
  let r := fun j => B.optimalScalarValue w c-(D j).optimalScalarValue w c
  have hCoarse (j) := B.directScheduled_coarse_measurableBand_score_tendsto hZero hS hb hSub (πc j)
    (B.markCutoff j) (B.terminal_lt_markCutoff j)
  have hTarget := B.truncatedValueRule_scorePayoffs_tendsto hZero hw hc id B.markCutoff B.terminal_lt_markCutoff
    tendsto_id B.markCutoff_tendsto (B.bandScore S) (B.bandScore_memLp_two hS hb hSub (Measure.dirac ()))
  have hMean (j) := B.directScheduled_coarse_payoffs_tendsto hZero (πc j) (B.markCutoff j) (B.terminal_lt_markCutoff j)
  have hV := B.directFiniteApproximation_value_tendsto hZero hw.le hc.le
  have hRegret (j) : Tendsto (fun m => Model.optimalScalarValue (P m) w c-(γ j m).scalarObjective (P m) w c)
      atTop (𝓝 (r j)) := by
    have hScalar := ((hMean j).1.const_mul w).add ((hMean j).2.const_mul c)
    have hExt : (πc j).extendToCountable B (B.terminal_lt_markCutoff j)=
        B.truncatedValuePolicy j (B.markCutoff j) (B.terminal_lt_markCutoff j) hw.le hc.le := rfl
    have hScalarEq : ((πc j).extendToCountable B (B.terminal_lt_markCutoff j)).scalarObjective w c=
        w*((πc j).extendToCountable B (B.terminal_lt_markCutoff j)).expectedReward+
        c*((πc j).extendToCountable B (B.terminal_lt_markCutoff j)).expectedDuration := rfl
    rw [← hScalarEq,hExt,
      B.truncatedValuePolicy_scalarObjective hZero j (B.markCutoff j) (B.terminal_lt_markCutoff j) hw hc.le] at hScalar
    have hScalar' : Tendsto (fun m => (γ j m).scalarObjective (P m) w c) atTop (𝓝 ((D j).optimalScalarValue w c)) := by
      apply hScalar.congr
      intro m
      exact ((γ j m).scalarObjective_eq (P m)
        ((P m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero m)) w c).symm
    exact hV.sub hScalar'
  have hRefine : Tendsto r atTop (𝓝 (0:ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => B.optimalScalarValue w c) atTop (𝓝 (B.optimalScalarValue w c)) := tendsto_const_nhds
    simpa only [r,D,id_eq,sub_self] using (hConst.sub
      (B.truncation_value_tendsto id B.markCutoff B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw.le hc.le))
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hProps (m) := B.directScheduledCloudScore_properties hZero hS hS0 m
  have hLimits := finiteCanonical_score_tendsto_of_coarse sizes P B.cap.property (lt_min hw hc)
    (by positivity : 0≤2*B.intensity.real S) (B.directFiniteApproximation_bounded hZero)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun m d hd => B.directFiniteApproximation_tailCount_le hZero m hd)
    (fun _ => w) (fun _ => c) (fun _ => min_le_left w c) (fun _ => min_le_right w c) (fun _ => hNorm)
    (B.directScheduledCloudScore hZero S) (fun m => (hProps m).1)
    (fun m i => Eventually.of_forall ((hProps m).2.1 i)) (fun m => (hProps m).2.2.1)
    (B.directScheduledCloudScore_information_le hZero hS hb hSub)
    γ bR bT r _ _ (fun j => (hCoarse j).1) (fun j => (hCoarse j).2) hTarget.1 hTarget.2 hRegret hRefine
  simpa only [P,hZero,NNReal.coe_zero] using hLimits
end ProphetSecretary.Limiting.CountableInstance
