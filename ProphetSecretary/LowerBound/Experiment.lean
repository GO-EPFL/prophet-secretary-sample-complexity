import ProphetSecretary.Model.LearnerConditioning
import ProphetSecretary.Analysis.MeasurableLinearResponse

/-!
# The finite perturbation experiment

The family below contains only laws, finite sizes, and weights. Its support,
normalization, information, and response properties are separate theorem
hypotheses. No existence or nondegeneracy claim is built into this data type.
The functions are the manuscript's `A_{m,π}`, `B_{m,π}`, and `r_m(π)` in
`thm:bayes`. Every policy is held fixed when the law parameter varies.
-/

open MeasureTheory Set
open ProphetSecretary.Model

namespace ProphetSecretary.LowerBound

structure Experiment where
  size : ℕ → ℕ
  law : ∀ m, ℝ → Instance (size m)
  weight : ℕ → ℝ

namespace Experiment

noncomputable def targetGap (E : Experiment) (m : ℕ) (π : RandomizedPolicy (E.size m))
    (θ lam : ℝ) : ℝ :=
  π.scalarObjective (E.law m θ) lam (1 - lam) -
    optimalCompetitiveRatio * (lam * (E.law m θ).expectedMaximum + 1 - lam)

noncomputable def baseWeightGap (E : Experiment) (m : ℕ) (π : RandomizedPolicy (E.size m))
    (θ : ℝ) : ℝ := E.targetGap m π θ (E.weight m)

noncomputable def balanceDifference (E : Experiment) (m : ℕ) (π : RandomizedPolicy (E.size m))
    (θ : ℝ) : ℝ :=
  π.expectedReward (E.law m θ) - π.expectedDuration (E.law m θ) -
    optimalCompetitiveRatio * ((E.law m θ).expectedMaximum - 1)

noncomputable def scalarRegret (E : Experiment) (m : ℕ) (π : RandomizedPolicy (E.size m)) : ℝ :=
  optimalScalarValue (E.law m 0) (E.weight m) (1 - E.weight m) -
    π.scalarObjective (E.law m 0) (E.weight m) (1 - E.weight m)

lemma targetGap_weight_shift (E : Experiment) (m : ℕ) (π : RandomizedPolicy (E.size m))
    {θ : ℝ} (hP : Integrable Instance.maximum (E.law m θ).valuesLaw) (v : ℝ) :
    E.targetGap m π θ (E.weight m + v) =
      E.baseWeightGap m π θ + v * E.balanceDifference m π θ := by
  unfold baseWeightGap targetGap balanceDifference
  rw [π.scalarObjective_eq _ hP, π.scalarObjective_eq _ hP]
  ring

lemma baseWeightGap_eq_optimum_sub_regret (E : Experiment) (m : ℕ)
    (π πopt : RandomizedPolicy (E.size m))
    (hopt : πopt.scalarObjective (E.law m 0) (E.weight m) (1 - E.weight m) =
      optimalScalarValue (E.law m 0) (E.weight m) (1 - E.weight m)) :
    E.baseWeightGap m π 0 = E.baseWeightGap m πopt 0 - E.scalarRegret m π := by
  unfold baseWeightGap targetGap scalarRegret
  rw [hopt]
  ring

lemma balanceDifference_sub (E : Experiment) (m : ℕ) (π πopt : RandomizedPolicy (E.size m)) :
    E.balanceDifference m π 0 - E.balanceDifference m πopt 0 =
      (π.expectedReward (E.law m 0) - π.expectedDuration (E.law m 0)) -
        (πopt.expectedReward (E.law m 0) - πopt.expectedDuration (E.law m 0)) := by
  unfold balanceDifference
  ring

lemma measurable_frozenBaseWeightGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw) :
    Measurable (fun d : Reservoir (E.size m) k × L.Seed =>
      E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ) :=
  (L.measurable_frozenScalarObjective _ hP measurable_const measurable_const).sub measurable_const

lemma measurable_frozenBalanceDifference (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ : ℝ) :
    Measurable (fun d : Reservoir (E.size m) k × L.Seed =>
      E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ) :=
  ((L.measurable_frozenExpectedReward _).sub (L.measurable_frozenExpectedDuration _)).sub measurable_const

lemma integrable_frozenBaseWeightGap (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw)
    (D : Measure (Reservoir (E.size m) k × L.Seed)) [IsProbabilityMeasure D] :
    Integrable (fun d => E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ) D :=
  (L.integrable_frozenScalarObjective _ hP D (E.weight m) (1 - E.weight m)).sub (integrable_const _)

lemma integrable_frozenBalanceDifference (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) (θ : ℝ)
    (hP : Integrable Instance.maximum (E.law m θ).valuesLaw)
    (D : Measure (Reservoir (E.size m) k × L.Seed)) [IsProbabilityMeasure D] :
    Integrable (fun d => E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ) D :=
  ((L.integrable_frozenExpectedReward _ hP D).sub (L.integrable_frozenExpectedDuration _ D)).sub
    (integrable_const _)

lemma measurable_frozenGapResponse (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) {C ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ θ ∈ Icc (0 : ℝ) ρ, Integrable Instance.maximum (E.law m θ).valuesLaw)
    (hTaylor : ∀ (π : RandomizedPolicy (E.size m)) θ, θ ∈ Icc (0 : ℝ) ρ →
      |E.baseWeightGap m π θ - E.baseWeightGap m π 0 -
        θ * deriv (E.baseWeightGap m π) 0| ≤ C * θ ^ 2) :
    Measurable (fun d : Reservoir (E.size m) k × L.Seed =>
      deriv (E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2)) 0) := by
  apply ProphetSecretary.Analysis.measurable_linearResponse
    (fun (θ : ℝ) (d : Reservoir (E.size m) k × L.Seed) =>
      E.baseWeightGap m (L.frozenRandomizedPolicy d.1 d.2) θ) _ hρ
  · intro θ hθ
    exact E.measurable_frozenBaseWeightGap m L θ (hP θ hθ)
  · intro d θ hθ
    exact hTaylor _ θ hθ

lemma measurable_frozenBalanceResponse (E : Experiment) (m : ℕ) {k : ℕ}
    (L : Learner (E.size m) k) {C ρ : ℝ} (hρ : 0 < ρ)
    (hTaylor : ∀ (π : RandomizedPolicy (E.size m)) θ, θ ∈ Icc (0 : ℝ) ρ →
      |E.balanceDifference m π θ - E.balanceDifference m π 0 -
        θ * deriv (E.balanceDifference m π) 0| ≤ C * θ ^ 2) :
    Measurable (fun d : Reservoir (E.size m) k × L.Seed =>
      deriv (E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2)) 0) := by
  apply ProphetSecretary.Analysis.measurable_linearResponse
    (fun (θ : ℝ) (d : Reservoir (E.size m) k × L.Seed) =>
      E.balanceDifference m (L.frozenRandomizedPolicy d.1 d.2) θ) _ hρ
  · intro θ _
    exact E.measurable_frozenBalanceDifference m L θ
  · intro d θ hθ
    exact hTaylor _ θ hθ

end Experiment
end ProphetSecretary.LowerBound
