import ProphetSecretary.Limiting.WeightedCoarseEmbedding
import ProphetSecretary.Limiting.HybridCanonicalZeroRejection

/-!
# A causal coarse comparison policy on the original finite instance

The static marginal ordering keeps the first K identities and the residual
block beginning at N. Independent zero clocks simulate padded identities.
This is an oracle comparison policy, with ordering fixed before execution;
it is not a learner supplied with unknown marginal laws.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n K : ℕ}

noncomputable def weightedCoarsePolicy (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (π : RandomizedHybridPolicy K) (d : ℝ) : Model.RandomizedPolicy n :=
  (((π.finiteCutoffEvaluation n d).ignoreExtras (weightedCoarseEmbedding n K N hKN)).simulateZeros).ignoreExtras
    (weightedMeanPermutation P wgt).toEmbedding

lemma weightedCoarsePolicy_expectedReward (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (π : RandomizedHybridPolicy K) (d : ℝ) :
    (weightedCoarsePolicy P wgt N hKN π d).expectedReward P=
      (π.finiteCutoffEvaluation n d).expectedReward
        ((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)) := by
  change ((((π.finiteCutoffEvaluation n d).ignoreExtras (weightedCoarseEmbedding n K N hKN)).simulateZeros).ignoreExtras
    (weightedMeanPermutation P wgt).toEmbedding).expectedReward P=_
  rw [Model.RandomizedPolicy.ignoreExtras_expectedReward,Model.RandomizedPolicy.simulateZeros_expectedReward,
    Model.RandomizedPolicy.ignoreExtras_expectedReward,weightedCoarse_restricted_instance]

lemma weightedCanonicalCoarsePolicy_expectedDuration (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (B : FiniteIntensityHybridInstance K) {w c : ℝ} (hw : 0<w) (hc : 0<c) (d : ℝ) :
    (weightedCoarsePolicy P wgt N hKN (B.valueThresholdPolicy hw.le hc.le) d).expectedDuration P=
      ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).expectedDuration
        ((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)) := by
  change (((((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).ignoreExtras
    (weightedCoarseEmbedding n K N hKN)).simulateZeros).ignoreExtras
    (weightedMeanPermutation P wgt).toEmbedding).expectedDuration P=_
  rw [Model.RandomizedPolicy.ignoreExtras_expectedDuration]
  rw [B.coarse_zero_simulation_expectedDuration hw hc n d (weightedCoarseEmbedding n K N hKN)]
  rw [Model.RandomizedPolicy.ignoreExtras_expectedDuration,weightedCoarse_restricted_instance]
end ProphetSecretary.Limiting
