import ProphetSecretary.LowerBound.Experiment
import ProphetSecretary.Model.TrainingZeroSimulation
import ProphetSecretary.Reach.GuaranteeScalar
import ProphetSecretary.Statistics.FullTrainingObservation

/-!
# Actual learner payoffs in the finite experiment

Conditioning is performed separately under each fixed online law. The two
hypotheses can have different online laws; no independence is asserted after
mixing the hidden sign. Scalar weights are analytical targets and are not inputs
to the learner. Removing appended zero identities preserves the hard budget.
-/

open MeasureTheory InformationTheory Set Filter
open ProphetSecretary.Model

namespace ProphetSecretary.LowerBound.Experiment

lemma scalarRegret_nonnegative (E : Experiment) (m : ℕ) (π : RandomizedPolicy (E.size m))
    (hP : Integrable Instance.maximum (E.law m 0).valuesLaw)
    (hw : E.weight m ∈ Icc (0 : ℝ) 1) : 0 ≤ E.scalarRegret m π :=
  sub_nonneg.mpr (scalarObjective_le_optimal π _ hP hw.1 (sub_nonneg.mpr hw.2))

theorem integral_frozenTargetGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ lam : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw)
    (D : Measure (Reservoir (E.size m) k × L.Seed)) [IsProbabilityMeasure D] :
    (∫ d, E.targetGap m (L.frozenRandomizedPolicy d.1 d.2) θ lam ∂D) =
      (L.randomizedPolicyWithDataLaw D).scalarObjective (E.law m θ) lam (1 - lam) -
        optimalCompetitiveRatio * (lam * (E.law m θ).expectedMaximum + 1 - lam) := by
  unfold targetGap
  rw [integral_sub (L.integrable_frozenScalarObjective _ hP D lam (1 - lam)) (integrable_const _),
    L.integral_frozenScalarObjective _ hP D lam (1 - lam)]
  simp only [integral_const, probReal_univ, one_smul]

theorem integral_shiftedFrozenGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ v : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw)
    (D : Measure (Reservoir (E.size m) k × L.Seed)) [IsProbabilityMeasure D] :
    (∫ d, E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ +
      v * E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ ∂D) =
      (L.randomizedPolicyWithDataLaw D).scalarObjective (E.law m θ) (E.weight m + v)
        (1 - (E.weight m + v)) - optimalCompetitiveRatio *
          ((E.weight m + v) * (E.law m θ).expectedMaximum + 1 - (E.weight m + v)) := by
  have heq : (∫ d, E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ +
      v * E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ ∂D) =
      ∫ d, E.targetGap m (L.frozenRandomizedPolicy d.1 d.2) θ (E.weight m + v) ∂D :=
    integral_congr_ae (Eventually.of_forall fun d => (E.targetGap_weight_shift m _ hP v).symm)
  rw [heq]
  exact E.integral_frozenTargetGap m L θ (E.weight m + v) hP D

/-- With the actual training law, the frozen-policy average is exactly the
learner's expected payoff, averaging both training and online randomness. -/
theorem integral_actualShiftedGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ v : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw) :
    (∫ d, E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ +
      v * E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ
        ∂((E.law m θ).reservoirLaw k).prod L.seedLaw) =
      (L.randomizedPolicy (E.law m θ)).scalarObjective (E.law m θ) (E.weight m + v)
        (1 - (E.weight m + v)) - optimalCompetitiveRatio *
          ((E.weight m + v) * (E.law m θ).expectedMaximum + 1 - (E.weight m + v)) :=
  E.integral_shiftedFrozenGap m L θ v hP _

/-- The information premise for the full-sampling completion also bounds the
raw data used in the conditional experiment, by an actual transcript decoder. -/
theorem rawTraining_information_le (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (t I : ℝ)
    (hInfo : klDiv (L.fullSampling.transcriptLaw (E.law m t))
      (L.fullSampling.transcriptLaw (E.law m (-t))) +
      klDiv (L.fullSampling.transcriptLaw (E.law m (-t)))
        (L.fullSampling.transcriptLaw (E.law m t)) ≤ ENNReal.ofReal I) :
    klDiv (((E.law m t).reservoirLaw k).prod L.seedLaw)
      (((E.law m (-t)).reservoirLaw k).prod L.seedLaw) +
      klDiv (((E.law m (-t)).reservoirLaw k).prod L.seedLaw)
        (((E.law m t).reservoirLaw k).prod L.seedLaw) ≤ ENNReal.ofReal I := by
  rwa [L.fullTraining_klDiv_eq, L.fullTraining_klDiv_eq] at hInfo

/-- Exact reward-to-scalar transfer for the base learner constructed by removing
observable zero identities. This holds even when the auxiliary mean is zero. -/
theorem removedZeros_shiftedGap_ge (E : Experiment) (m : ℕ) {N k : ℕ}
    (L : Learner (E.size m + N) k) {ε H : ℝ}
    (hGuarantee : L.Guarantees (optimalCompetitiveRatio - ε)) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (θ v : ℝ) (hbound : ∀ i, ∀ᵐ x ∂(E.law m θ).law i, x ≤ H)
    (hN : 0 < N) (hw : 0 ≤ E.weight m + v) (hc : 0 ≤ 1 - (E.weight m + v)) :
    -ε * (H + 1) - 20 / Real.sqrt (N : ℝ) ≤
      (∫ d, E.baseWeightGap m (L.removeZeros.frozenRandomizedPolicy d.1 d.2) θ +
        v * E.balanceDifference m (L.removeZeros.frozenRandomizedPolicy d.1 d.2) θ
          ∂((E.law m θ).reservoirLaw k).prod L.removeZeros.seedLaw) := by
  have hP := (E.law m θ).integrable_maximum_of_bounded hbound
  rw [E.integral_actualShiftedGap m L.removeZeros θ v hP]
  have hbase := L.padded_scalarGap_ge hGuarantee (E.law m θ) hH hbound hε hN hw hc (by ring)
  have hsim := L.removeZeros_scalarObjective (E.law m θ) hP hc (w := E.weight m + v)
  linarith

end ProphetSecretary.LowerBound.Experiment
