import ProphetSecretary.Limiting.WeightedCoarseScore
import ProphetSecretary.Probability.NormalizedScoreResponse

/-!
# Original complete-score expectations of the coarse comparison policy

A proved pointwise score pullback identifies the analytical complete score
on the original array. Product integrability is transported through the
actual padding, projection and relabeling maps.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n K : ℕ}

lemma weightedCanonicalCoarsePolicy_expectedScores_of_pullback
    (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ) (hKN : K≤N)
    (B : FiniteIntensityHybridInstance K) {w c : ℝ} (hw : 0<w) (hc : 0<c) (d : ℝ)
    (s : (Fin (K+n) → ℝ) → ℝ) (hs : Measurable s) (h : Fin n → ℝ → ℝ)
    (hEq : ∀ x, weightedCoarseScore P wgt N hKN s x=completeScore h x)
    (hRInt : Integrable (fun ω : ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).World =>
      s ω.1*((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).realizedReward ω)
      (((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw (Measure.dirac ())))
    (hTInt : Integrable (fun ω : ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).World =>
      s ω.1*((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).realizedDuration ω)
      (((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw (Measure.dirac ()))) :
    let π := B.valueThresholdPolicy hw.le hc.le
    let γ := weightedCoarsePolicy P wgt N hKN π d
    γ.expectedRewardScore P h=(∫ ω : (π.finiteCutoffEvaluation n d).World,
      s ω.1*(π.finiteCutoffEvaluation n d).realizedReward ω
      ∂((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw π.seedLaw) ∧
    γ.expectedDurationScore P h=(∫ ω : (π.finiteCutoffEvaluation n d).World,
      s ω.1*(π.finiteCutoffEvaluation n d).realizedDuration ω
      ∂((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw π.seedLaw) := by
  have hR := weightedCoarsePolicy_score_reward P wgt N hKN (B.valueThresholdPolicy hw.le hc.le) d s hs hRInt
  have hT := weightedCanonicalCoarsePolicy_score_duration P wgt N hKN B hw hc d s hs hTInt
  constructor
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
      congrArg (fun x => x*(weightedCoarsePolicy P wgt N hKN (B.valueThresholdPolicy hw.le hc.le) d).realizedReward ω)
        (hEq ω.1).symm))).trans hR.2
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
      congrArg (fun x => x*(weightedCoarsePolicy P wgt N hKN (B.valueThresholdPolicy hw.le hc.le) d).realizedDuration ω)
        (hEq ω.1).symm))).trans hT.2
end ProphetSecretary.Limiting
