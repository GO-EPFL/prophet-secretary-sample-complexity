import ProphetSecretary.LowerBound.ConditionalExperiment
import ProphetSecretary.Model.ScalarSlopeStability
import ProphetSecretary.Statistics.BinaryExperimentTaylor

/-!
# The finite Bayesian experiment bound

The observed data have their actual full-training laws. Fixed-policy responses
are evaluated at the base law, whereas the learned target gap averages training
and online randomness from the current law. The analytical target weight is
hidden from the learner. Paper correspondence: the uniform experiment estimate
inside `thm:bayes`; the inverse-linear contradiction is a subsequent step.
-/

open MeasureTheory InformationTheory Set Filter
open ProphetSecretary.Model
open scoped ENNReal

namespace ProphetSecretary.LowerBound.Experiment

/-- The learned target gap includes training from the current law. Its
parameter-dependent learned policy is never differentiated below. -/
noncomputable def trainedTargetGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ v : ℝ) : ℝ :=
  E.targetGap m (L.randomizedPolicy (E.law m θ)) θ (E.weight m + v)

theorem integral_shiftedGap_eq_trainedTargetGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ v : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw) :
    (∫ d, E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ +
      v * E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ
        ∂((E.law m θ).reservoirLaw k).prod L.seedLaw) = E.trainedTargetGap m L θ v :=
  E.integral_actualShiftedGap m L θ v hP

theorem removedZeros_trainedTargetGap_ge (E : Experiment) (m : ℕ) {N k : ℕ}
    (L : Learner (E.size m + N) k) {ε H : ℝ}
    (hGuarantee : L.Guarantees (optimalCompetitiveRatio - ε)) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (θ v : ℝ) (hbound : ∀ i, ∀ᵐ x ∂(E.law m θ).law i, x ≤ H)
    (hN : 0 < N) (hw : 0 ≤ E.weight m + v) (hc : 0 ≤ 1 - (E.weight m + v)) :
    -ε * (H + 1) - 20 / Real.sqrt (N : ℝ) ≤ E.trainedTargetGap m L.removeZeros θ v := by
  have h := E.removedZeros_shiftedGap_ge m L hGuarantee hε hH θ v hbound hN hw hc
  rwa [E.integral_shiftedGap_eq_trainedTargetGap m L.removeZeros θ v
    ((E.law m θ).integrable_maximum_of_bounded hbound)] at h

/-- The two-law estimate for an actual learner. The information, Taylor, and
response assumptions are exactly the corresponding hypotheses of `thm:bayes`,
at the displayed m,t. Every constant is independent of the number of offers. -/
theorem binary_experiment_upper (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (πopt : RandomizedPolicy (E.size m))
    {α H v t I C B b : ℝ} (hα : 0 < α) (hH : 0 ≤ H) (hv : 0 ≤ v) (ht : 0 ≤ t) (hI : 0 ≤ I)
    (hweight : E.weight m ∈ Icc α (1 - α))
    (hbound : ∀ i, ∀ᵐ x ∂(E.law m 0).law i, x ≤ H)
    (hPplus : Integrable Instance.maximum (E.law m t).valuesLaw)
    (hPminus : Integrable Instance.maximum (E.law m (-t)).valuesLaw)
    (hopt : πopt.scalarObjective (E.law m 0) (E.weight m) (1 - E.weight m) =
      optimalScalarValue (E.law m 0) (E.weight m) (1 - E.weight m))
    (ω : ℝ → ℝ) (hB : 0 ≤ B) (hmono : Monotone ω)
    (hω : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B)
    (hInfo : klDiv (L.fullSampling.transcriptLaw (E.law m t))
      (L.fullSampling.transcriptLaw (E.law m (-t))) +
      klDiv (L.fullSampling.transcriptLaw (E.law m (-t)))
        (L.fullSampling.transcriptLaw (E.law m t)) ≤ ENNReal.ofReal (I * (k : ℝ) * t ^ 2))
    (hTaylor : ∀ π : RandomizedPolicy (E.size m),
      (|E.baseWeightGap m π t - E.baseWeightGap m π 0 - t * deriv (E.baseWeightGap m π) 0| ≤ C * t ^ 2) ∧
      (|E.baseWeightGap m π (-t) - E.baseWeightGap m π 0 + t * deriv (E.baseWeightGap m π) 0| ≤ C * t ^ 2) ∧
      (|E.balanceDifference m π t - E.balanceDifference m π 0 - t * deriv (E.balanceDifference m π) 0| ≤ C * t ^ 2) ∧
      (|E.balanceDifference m π (-t) - E.balanceDifference m π 0 + t * deriv (E.balanceDifference m π) 0| ≤ C * t ^ 2))
    (hResponse : ∀ π : RandomizedPolicy (E.size m),
      |deriv (E.baseWeightGap m π) 0 - deriv (E.baseWeightGap m πopt) 0| +
      |deriv (E.balanceDifference m π) 0 - deriv (E.balanceDifference m πopt) 0| ≤ ω (E.scalarRegret m π))
    (hNegative : deriv (E.balanceDifference m πopt) 0 ≤ -b) :
    (1 / 2 : ℝ) * E.trainedTargetGap m L t v +
      (1 / 2 : ℝ) * E.trainedTargetGap m L (-t) (-v) ≤
        E.baseWeightGap m πopt 0 - v * b * t +
        ((scalarSlopeConstant α (1 - α) H * v) ^ 2 / 8) * (I * (k : ℝ) * t ^ 2) +
        ProphetSecretary.Statistics.bayesModulusError ω (1 + v) B t + (1 + v) * C * t ^ 2 := by
  let μ := ((E.law m t).reservoirLaw k).prod L.seedLaw
  let ν := ((E.law m (-t)).reservoirLaw k).prod L.seedLaw
  let π : Reservoir (E.size m) k × L.Seed → RandomizedPolicy (E.size m) :=
    fun d => L.frozenRandomizedPolicy d.1 d.2
  let Ap := fun d => E.baseWeightGap m (π d) t
  let Am := fun d => E.baseWeightGap m (π d) (-t)
  let Bp := fun d => E.balanceDifference m (π d) t
  let Bm := fun d => E.balanceDifference m (π d) (-t)
  let A₀ := fun d => E.baseWeightGap m (π d) 0
  let B₀ := fun d => E.balanceDifference m (π d) 0
  let DA := fun d => deriv (E.baseWeightGap m (π d)) 0
  let DB := fun d => deriv (E.balanceDifference m (π d)) 0
  let r := fun d => E.scalarRegret m (π d)
  have hP := (E.law m 0).integrable_maximum_of_bounded hbound
  have hweight01 : E.weight m ∈ Icc (0 : ℝ) 1 :=
    ⟨hα.le.trans hweight.1, hweight.2.trans (by linarith)⟩
  have hpInt (D : Measure (Reservoir (E.size m) k × L.Seed)) [IsProbabilityMeasure D] :
      Integrable (fun d => Ap d + v * Bp d) D :=
    (E.integrable_frozenBaseWeightGap m L t hPplus D).add
      ((E.integrable_frozenBalanceDifference m L t hPplus D).const_mul v)
  have hmInt (D : Measure (Reservoir (E.size m) k × L.Seed)) [IsProbabilityMeasure D] :
      Integrable (fun d => Am d - v * Bm d) D :=
    (E.integrable_frozenBaseWeightGap m L (-t) hPminus D).sub
      ((E.integrable_frozenBalanceDifference m L (-t) hPminus D).const_mul v)
  have hregret : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, 0 ≤ r d :=
    Eventually.of_forall fun d => E.scalarRegret_nonnegative m (π d) hP hweight01
  have hbase : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν,
      A₀ d = E.baseWeightGap m πopt 0 - r d :=
    Eventually.of_forall fun d => E.baseWeightGap_eq_optimum_sub_regret m (π d) πopt hopt
  have hslope : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν,
      |B₀ d - E.balanceDifference m πopt 0| ≤
        scalarSlopeConstant α (1 - α) H * Real.sqrt (r d) := by
    filter_upwards [] with d
    change |E.balanceDifference m (π d) 0 - E.balanceDifference m πopt 0| ≤ _
    rw [E.balanceDifference_sub]
    exact (π d).rewardDurationSlope_stability πopt _ hα (by linarith) hH hbound hweight hopt
  have hinfo := E.rawTraining_information_le m L t (I * (k : ℝ) * t ^ 2) hInfo
  have hIt : 0 ≤ I * (k : ℝ) * t ^ 2 := by positivity
  have hstat := ProphetSecretary.Statistics.binary_experiment_gap_of_taylor μ ν ω hv hB ht hIt hmono hω hinfo
    Ap Am Bp Bm A₀ B₀ DA DB r (hpInt μ) (hpInt ν) (hmInt μ) (hmInt ν) hregret hbase
    (Eventually.of_forall fun d => (hTaylor (π d)).1)
    (Eventually.of_forall fun d => (hTaylor (π d)).2.1)
    (Eventually.of_forall fun d => (hTaylor (π d)).2.2.1)
    (Eventually.of_forall fun d => (hTaylor (π d)).2.2.2)
    hslope (Eventually.of_forall fun d => hResponse (π d)) hNegative
  have hpEq := E.integral_shiftedGap_eq_trainedTargetGap m L t v hPplus
  have hmEq : (∫ d, E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) (-t) -
      v * E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) (-t) ∂ν) =
      E.trainedTargetGap m L (-t) (-v) := by
    simpa only [neg_mul, sub_eq_add_neg] using
      E.integral_shiftedGap_eq_trainedTargetGap m L (-t) (-v) hPminus
  dsimp only [Ap, Am, Bp, Bm, π] at hstat
  rw [hpEq, hmEq] at hstat
  exact hstat

end ProphetSecretary.LowerBound.Experiment
