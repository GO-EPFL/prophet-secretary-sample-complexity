import ProphetSecretary.Statistics.MixedSelectedRegretAlmostSure
import ProphetSecretary.Statistics.MixedOptimism

/-!
# Exact known marginals in empirical scalar optimization

Paper correspondence: the known-distribution extension following `upstat:main`.
Known identities retain their true laws and every other identity uses its stored
empirical law. The same explicit constant works before choosing the finite
instance, known set, sample count, selector or independent auxiliary randomness.
Integrability is explicit. The learner's complete behavior is invariant under
changes of undeclared unknown laws, and its budget holds on every outcome.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model

/-- The supplied instance is only a representation of the declared known laws:
changing any undeclared marginal leaves the entire causal learner unchanged. -/
theorem Learner.mixedEmpiricalWithSelectedWeights_congr_known {n k : ℕ} [NeZero k]
    (D E : Instance n) (hD : Integrable Instance.maximum D.valuesLaw)
    (hE : Integrable Instance.maximum E.valuesLaw) (known : Finset (Fin n))
    (hknown : ∀ i∈known, D.law i=E.law i) (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C) :
    Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC =
      Learner.mixedEmpiricalWithSelectedWeights E hE known Seed ν W C hW hC := by
  unfold Learner.mixedEmpiricalWithSelectedWeights
  congr 1
  exact mixedEmpiricalSelectedPolicy_congr_known known hknown W C

/-- Both displayed conclusions of `upstat:main` remain valid when any fixed
set of marginals is known exactly, with the SAME interval-dependent constant. -/
theorem knownMarginalScalarOptimization {lo hi : ℝ} (hlo : 0<lo) (hlohi : lo≤hi) :
    ∃ K : ℝ, 0<K ∧
      (∀ (n k : ℕ) [NeZero k] (P : Instance n)
        (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n))
        (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z),
        (∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p∈Icc lo hi) →
        (let L := Learner.mixedEmpiricalWithSelectedWeights P (P.integrable_maximum_of_bounded hbound) known
          Seed ν (fun _ => 1) Z measurable_const hZ
         let F := fun p => optimalScalarValue P 1 (Z p)-(L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
         Integrable F ((P.reservoirLaw k).prod ν) ∧
          (∫ p, F p ∂(P.reservoirLaw k).prod ν)≤K*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ)) ∧
        (∀ (y : Reservoir n k) (r : Seed) (i : Fin n),
          requests (trainingTranscript
            (Learner.mixedEmpiricalWithSelectedWeights P (P.integrable_maximum_of_bounded hbound) known
              Seed ν (fun _ => 1) Z measurable_const hZ).request r y) i≤k)) ∧
      (∀ (n k : ℕ) [NeZero k] (P : Instance n)
        (_hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n)) (z : ℝ), z∈Icc lo hi →
        Integrable (fun y : Reservoir n k => optimalScalarValue (mixedEmpiricalInstance P known y) 1 z) (P.reservoirLaw k) ∧
        0≤(∫ y : Reservoir n k, optimalScalarValue (mixedEmpiricalInstance P known y) 1 z ∂P.reservoirLaw k)-
          optimalScalarValue P 1 z ∧
        (∫ y : Reservoir n k, optimalScalarValue (mixedEmpiricalInstance P known y) 1 z ∂P.reservoirLaw k)-
          optimalScalarValue P 1 z≤K*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ)) := by
  refine ⟨empiricalCandidateRegretConstant lo hi,empiricalCandidateRegretConstant_positive hlo hlohi,?_,?_⟩
  · intro n k hk P hbound known Seed hSeed ν hν Z hZ hZrange
    exact ⟨Learner.mixedSelectedScalar_expected_regret_integrable_bound_ae P known hbound ν hZ hlo hlohi hZrange,
      fun y r i => Learner.mixedEmpiricalWithSelectedWeights_hardBudget P (P.integrable_maximum_of_bounded hbound)
        known Seed ν (fun _ => 1) Z measurable_const hZ y r i⟩
  · intro n k hk P hbound known z hz
    exact ⟨integrable_mixedScalarValue_reservoir P known hbound (hlo.trans_le hz.1).le,
      mixedScalarValue_expected_optimism_bound_reservoir P known hbound hlo hlohi hz⟩

end ProphetSecretary.Model
