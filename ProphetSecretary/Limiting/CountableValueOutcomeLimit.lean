import ProphetSecretary.Limiting.CountableValueOutcomeEvalLimit

/-!
# Actual outcome convergence of canonical finite truncations

A common acceptance floor and actual positive-level local finiteness promote
pointwise strict-margin decisions to reward/duration convergence on the common
countable world. Thus this outcome limit is proved independently of scalar
value convergence and of any optimizing-policy convergence assumption.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

theorem valueRule_truncation_outcomes_tendsto_ae (B : CountableInstance) (hZero : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      Tendsto (fun N => (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedReward B.terminal v)
        atTop (𝓝 ((B.valueRule w c).realizedReward B.terminal v)) ∧
      Tendsto (fun N => (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedDuration v)
        atTop (𝓝 ((B.valueRule w c).realizedDuration v)) :=
  B.valueRule_truncation_outcomes_eval_tendsto_ae hZero B hZero hw hc

end ProphetSecretary.Limiting.CountableInstance
