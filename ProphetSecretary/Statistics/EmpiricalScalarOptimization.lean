import ProphetSecretary.Statistics.SelectedScalarAlmostSureRange
import ProphetSecretary.Statistics.EmpiricalOptimismRate

/-!
# Empirical scalar optimization (`upstat:main`)

For any fixed positive compact scalar interval, one explicit finite constant
works simultaneously for every finite independent cap-one instance and every
positive sample count. It controls both the true regret of the empirical
optimizer at a training-selected scalar and the separate fixed-scalar upward
bias. The empirical learner's budget holds on every training outcome.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

/-- Paper theorem `upstat:main`. Its constant is chosen before the instance,
its size, sample count, scalar selector and independent auxiliary probability
space. The optional extension allowing exact known marginals is separate. -/
theorem empiricalScalarOptimization {lo hi : ℝ} (hlo : 0<lo) (hlohi : lo≤hi) :
    ∃ K : ℝ, 0<K ∧
      (∀ (n k : ℕ) [NeZero k] (P : Instance n)
        (_hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1)
        (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z),
        (∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p∈Icc lo hi) →
        ((∫ p, optimalScalarValue P 1 (Z p)-
          ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ∂(P.reservoirLaw k).prod ν) ≤ K*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ)) ∧
        (∀ (y : Reservoir n k) (r : Seed) (i : Fin n),
          requests (trainingTranscript
            (Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).request r y) i ≤ k)) ∧
      (∀ (n k : ℕ) [NeZero k] (P : Instance n)
        (_hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (z : ℝ), z∈Icc lo hi →
        0 ≤ (∫ y : Reservoir n k, optimalScalarValue (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw k)-
            optimalScalarValue P 1 z ∧
        (∫ y : Reservoir n k, optimalScalarValue (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw k)-
            optimalScalarValue P 1 z ≤ K*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ)) := by
  refine ⟨empiricalCandidateRegretConstant lo hi,empiricalCandidateRegretConstant_positive hlo hlohi,?_,?_⟩
  · intro n k hk P hbound Seed hSeed ν hν Z hZ hZrange
    exact ⟨Learner.empiricalSelectedScalar_expected_regret_le_ae P hbound ν hZ hlo hlohi hZrange,
      fun y r i => Learner.empiricalWithSelectedWeights_hardBudget Seed ν (fun _ => 1) Z measurable_const hZ y r i⟩
  · intro n k hk P hbound z hz
    exact empiricalScalarValue_expected_optimism_bound_reservoir P hbound hlo hlohi hz

end ProphetSecretary.Model
