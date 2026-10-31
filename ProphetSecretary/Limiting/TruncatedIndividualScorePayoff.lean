import ProphetSecretary.Limiting.TruncatedScorePayoffTransport
import ProphetSecretary.Probability.CenteredBoundedScore

/-!
# Exact individual-score covariance transport for countable truncations

A retained score depends on the same original individual in the hybrid and
full executions. The complete-score product is preserved by the actual
finite observer projection, including its independent online clocks.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability
variable {N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.integral_individualScorePayoffs_eq_extended
    (π : HybridRule N Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal:ℝ)<b)
    (i : Fin N) (f : ℝ →ᵇ ℝ) :
    ((∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i)*π.realizedReward B.terminal v
      ∂(B.truncation N b hb).law ν)=
      ∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i.val)*
        (extendTruncatedRule π b).realizedReward B.terminal v ∂B.completeWorldLaw ν) ∧
    ((∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i)*π.realizedDuration v
      ∂(B.truncation N b hb).law ν)=
      ∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i.val)*
        (extendTruncatedRule π b).realizedDuration v ∂B.completeWorldLaw ν) := by
  let G : FiniteObserverWorld N Seed → ℝ := fun q => centeredBoundedScore
    (B.individuals i.val:Measure ℝ) f (q.2.1 i)
  have hG : Measurable G := (continuous_centeredBoundedScore (B.individuals i.val:Measure ℝ) f).measurable.comp
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  exact π.integral_scoredPayoffs_eq_extended hπ B ν hb G hG
end ProphetSecretary.Limiting
