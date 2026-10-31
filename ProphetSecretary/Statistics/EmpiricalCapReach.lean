import ProphetSecretary.Model.EmpiricalCapPolicy
import ProphetSecretary.Reach.MarkovStrict

/-!
# True reach dominates duration for the modified empirical policy

The empirical threshold is deletion-monotone for every training outcome.
It is evaluated under the true independent online product law. The data
law may be arbitrary, but remains independent of online offers and clocks.
Paper correspondence: the reach comparison in `eq:bayes-target-score`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Learner.empiricalCapAcceptance_policy (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).policy=empiricalCapSelectedPolicy Z := by
  apply congrArg Policy.mk
  funext p t i x H
  rcases p with ⟨y,r⟩
  exact Learner.empiricalCapAcceptance_decide Seed ν Z hZ y r t i x H

theorem Learner.empiricalCapAcceptance_meanDuration_le_reach_under (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (P : Instance n) (D : Measure (Reservoir n k × Seed)) [IsProbabilityMeasure D] (i : Fin n) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.meanDuration P D≤
      (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.reachProbability P D i := by
  rw [Learner.empiricalCapAcceptance_policy]
  exact markovPolicy.meanDuration_le_reachProbability _ (empiricalCapSelectedPolicy_deletionMonotone Z)
    (empiricalCapSelectedPolicy_isMeasurable hZ) P D i

theorem Learner.empiricalCapAcceptance_meanDuration_le_reach (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (P : Instance n) (i : Fin n) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).meanDuration P≤
      (Learner.empiricalCapAcceptance Seed ν Z hZ).reachProbability P i :=
  Learner.empiricalCapAcceptance_meanDuration_le_reach_under Seed ν Z hZ P ((P.reservoirLaw k).prod ν) i

end ProphetSecretary.Model
