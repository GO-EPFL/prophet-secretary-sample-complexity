import ProphetSecretary.Limiting.DirectUnscaledIndividualScores
import ProphetSecretary.Limiting.DirectCenteredBandCountCoarse

/-!
# Coarse policies (`lem:coarse-policy`)

Fix a retained finite prefix and a positive observation cutoff. The actual
callback is deployed on the original direct approximants by the causal
identity projection `directCoarsePolicy`. Its reward and duration converge by
`coarse_policy` below. Joint expectations for every literal centered bounded
continuous retained-individual score are given by
`directScheduled_coarse_unscaled_individual_score_tendsto`.
Joint expectations for every measurable Poisson band bounded away from zero
are given by `directScheduled_coarse_centeredBandCount_tendsto`; hence they
cover all positive continuity bands, including finite windows and bands
crossing the observation cutoff. The corresponding zero-atom likelihood-score limits are proved separately.
The band-count theorem permits any
fixed randomized hybrid callback. Its limiting rule is the extension of that
same callback, with the same independent auxiliary law.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance

 theorem coarse_policy (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℕ) (d : ℝ) (hd : (B.terminal:ℝ)<d) {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    let π := (B.truncation K d hd).valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedReward
      (B.directFiniteApproximation hZero m)) atTop
      (𝓝 ((π.extendToCountable B hd).expectedReward)) ∧
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDuration
      (B.directFiniteApproximation hZero m)) atTop
      (𝓝 ((π.extendToCountable B hd).expectedDuration)) :=
  B.directScheduled_coarse_payoffs_tendsto hZero _ d hd
end ProphetSecretary.Limiting.CountableInstance
