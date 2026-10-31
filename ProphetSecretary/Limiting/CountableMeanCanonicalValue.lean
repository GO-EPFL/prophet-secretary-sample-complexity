import ProphetSecretary.Limiting.CountableMeanPolicyTransport
import ProphetSecretary.Limiting.CountableFixedValuePolicy
import ProphetSecretary.Limiting.CountableCanonicalOptimizer

/-!
# Scalar value is preserved by a zero-response individual mean contraction

The original canonical callback is admissible under the contracted law by
its positive linear acceptance floor. Its expected reward and duration are
preserved by the supported-hull constancy theorem. In the other direction,
every contracted-law competing policy has the causal mean-substitution
simulator. Thus equality concerns the full scalar supremum, with no assumed
convergence of optimizers or restriction of competing policies.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def fixedCanonicalMeanPolicy (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ) : RandomizedCountablePolicy (B.contractIndividual i) :=
  B.fixedValuePolicy (B.contractIndividual i) (by rw [contractIndividual_terminal]) hw hc

theorem fixedCanonicalMeanPolicy_expectedReward (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.fixedCanonicalMeanPolicy hw hc i).expectedReward=(B.valuePolicy hw hc).expectedReward := by
  have hMP := B.meanSubstitution_measurePreserving i (Measure.dirac ())
  have hMap := hMP.hasLaw.integral_comp ((B.valueRule w c).measurable_realizedReward
    (B.valueRule_isMeasurable hw.le hc.le) B.terminal).aestronglyMeasurable
  have hMean := B.canonical_integral_reward_mean_substitution_eq hZero hw hc i hScores
  exact hMap.symm.trans hMean

theorem fixedCanonicalMeanPolicy_expectedDuration (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.fixedCanonicalMeanPolicy hw hc i).expectedDuration=(B.valuePolicy hw hc).expectedDuration := by
  have hMP := B.meanSubstitution_measurePreserving i (Measure.dirac ())
  have hMap := hMP.hasLaw.integral_comp ((B.valueRule w c).measurable_realizedDuration
    (B.valueRule_isMeasurable hw.le hc.le)).aestronglyMeasurable
  exact hMap.symm.trans (integral_congr_ae (B.canonical_durationAtValue_mean_ae_eq hZero hw hc i hScores))

theorem fixedCanonicalMeanPolicy_scalarObjective (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.fixedCanonicalMeanPolicy hw hc i).scalarObjective w c=(B.valuePolicy hw hc).scalarObjective w c := by
  rw [RandomizedCountablePolicy.scalarObjective,RandomizedCountablePolicy.scalarObjective,
    B.fixedCanonicalMeanPolicy_expectedReward hZero hw hc i hScores,
    B.fixedCanonicalMeanPolicy_expectedDuration hZero hw hc i hScores]

theorem contractIndividual_value_eq_of_zero_duration_scores
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.contractIndividual i).optimalScalarValue w c=B.optimalScalarValue w c := by
  apply le_antisymm (B.contractIndividual_value_le i w c)
  rw [← B.valuePolicy_optimal hZero hw hc,
    ← B.fixedCanonicalMeanPolicy_scalarObjective hZero hw hc i hScores]
  exact (B.contractIndividual i).scalarObjective_le_value (B.fixedCanonicalMeanPolicy hw hc i) w c

end ProphetSecretary.Limiting.CountableInstance
