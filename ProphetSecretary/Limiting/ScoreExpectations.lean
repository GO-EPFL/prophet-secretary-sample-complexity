import ProphetSecretary.Limiting.DirectScoreBounds
import ProphetSecretary.Limiting.DirectScheduledBandScoreL2

/-!
# Complete score expectations (`lem:score-expectations`)

The direct approximants and their canonical policies are the actual policies
of the full finite online model. `score_expectations_cloud` proves reward,
duration and maximum covariance convergence for every measurable positive
band, and therefore for every continuity band in the manuscript.

For an arbitrary bounded continuous individual observable, the literal
centered score and all three limits are given by
`directScheduled_unscaled_individual_score_limits`. The exact complete-vector
score formula is `directUnscaledIndividualScore_complete`; its second moment
is at most `boundedScoreScale f ^ 2`. Cloud second moments are at most twice
the band's intensity. Both bounds hold before the array index is chosen.
`directScheduled_bandScore_count_error_tendsto` proves the stated vanishing
squared error between the likelihood score and its centered total count.

`directScheduled_unscaled_individual_regret_stability` and
`directScheduled_cloud_score_regret_stability` give a single modulus uniform
over the index, every competing admissible randomized policy and its
independent seed. They use raw scalar regret for arbitrary positive fixed
weights. The complete score may depend on observations after stopping only
as an analytical multiplier in the expectation.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

 theorem score_expectations_cloud (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximumScore (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (B.prophetBandLikelihoodDerivative S)) := by
  have h := B.directScheduled_canonical_measurableBand_score_limits_positive hZero hS hb hSub hw hc
  exact ⟨h.1,h.2,B.directScheduled_cloud_expectedMaximumScore_tendsto hZero hS hb hSub⟩
end ProphetSecretary.Limiting.CountableInstance
