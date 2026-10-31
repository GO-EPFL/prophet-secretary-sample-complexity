import ProphetSecretary.Model.EmpiricalLearner
import ProphetSecretary.Statistics.CanonicalRegretCandidateBound

/-!
# Frozen empirical learner equals the canonical design rule on every history

Empirical optimality under the empirical law alone would not identify behavior
under the true law. The equality here is pointwise for every identity, value,
time and history at every valid training outcome, so it transfers the frozen
learner's objective under ANY evaluation instance. Training-selected weights
and the learner's hard budget remain unchanged.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Learner.empiricalWithSelectedWeights_frozen_rule_eq (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0<W (y,r)) (hc : 0≤C (y,r)) :
    (Learner.empiricalWithSelectedWeights Seed ν W C hW hC).frozenRule y r =
      ((totalEmpiricalInstance y).valuePolicy (totalEmpiricalInstance_integrable y) hw.le hc).rule := by
  have hdec : ((Learner.empiricalWithSelectedWeights Seed ν W C hW hC).frozenRule y r).decide =
      ((totalEmpiricalInstance y).valuePolicy (totalEmpiricalInstance_integrable y) hw.le hc).rule.decide := by
    funext s t i x h
    cases s
    exact Learner.empiricalWithSelectedWeights_decide Seed ν W C hW hC y r hw hc t i x h
  exact congrArg Policy.mk hdec

/-- Evaluation-law transfer follows from exact decisions, not just design-law
optimality. Both objectives retain the same physical duration convention. -/
theorem Learner.empiricalWithSelectedWeights_frozen_objective_eq (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0<W (y,r)) (hc : 0≤C (y,r))
    (P : Instance n) (w c : ℝ) :
    ((Learner.empiricalWithSelectedWeights Seed ν W C hW hC).frozenRandomizedPolicy y r).scalarObjective P w c =
      ((totalEmpiricalInstance y).valuePolicy (totalEmpiricalInstance_integrable y) hw.le hc).scalarObjective P w c := by
  have hRule := Learner.empiricalWithSelectedWeights_frozen_rule_eq Seed ν W C hW hC y r hw hc
  change (∫ ω : World n Unit,
    w*((Learner.empiricalWithSelectedWeights Seed ν W C hW hC).frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    c*((Learner.empiricalWithSelectedWeights Seed ν W C hW hC).frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) = _
  rw [hRule]
  rfl

/-- Candidate-integral regret bound for the actual law-independent empirical
learner with a sample-selected scalar, at each training outcome. -/
theorem Learner.empiricalSelectedScalar_frozen_regret_bound (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) (hz : 0≤Z (y,r))
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    optimalScalarValue P 1 (Z (y,r))-
      ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy y r).scalarObjective
        P 1 (Z (y,r)) ≤
      ∑ i, ∫ u, candidateLossMean (totalEmpiricalInstance y) P (totalEmpiricalInstance_integrable y) (Z (y,r)) hz i u ∂Instance.clocksLaw n := by
  rw [Learner.empiricalWithSelectedWeights_frozen_objective_eq Seed ν (fun _ => 1) Z measurable_const hZ y r zero_lt_one hz]
  exact (totalEmpiricalInstance y).canonical_regret_le_sum_candidateLossMean P (totalEmpiricalInstance_integrable y) hP hz

end ProphetSecretary.Model
