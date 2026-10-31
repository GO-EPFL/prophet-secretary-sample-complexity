import ProphetSecretary.Statistics.SelectedCandidateRate
import ProphetSecretary.Statistics.SelectedRegretCandidateReduction

/-!
# Expected regret at a training-selected scalar (`upstat:selected`)

The explicit constant depends only on the fixed positive scalar interval.
It is uniform in the number of independent offers, their laws, the sample
count, the measurable scalar selection function and independent auxiliary
randomness. The implemented empirical learner has a hard per-marginal budget.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type} [MeasurableSpace Seed]

/-- The sample-selected part of `upstat:main`, for a scalar selector taking
values in its prescribed interval on every training and seed outcome. -/
theorem Learner.empiricalSelectedScalar_expected_regret_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ∂(P.reservoirLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi * P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  have h0 : ∀ p, Z p∈Icc (0:ℝ) hi := fun p => ⟨(hlo.trans_le (hZrange p).1).le,(hZrange p).2⟩
  apply (Learner.empiricalSelectedScalar_integral_regret_le_candidates P hbound ν hZ h0).trans
  calc
    _ ≤ ∑ i : Fin n, empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)*
        (∫ x, x ∂P.law i)/(k:ℝ) :=
      Finset.sum_le_sum fun i _ => integral_selectedCandidateContribution_rate_full P hbound hZ hlo hlohi hZrange i ν
    _ = ∑ i : Fin n, (empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)/(k:ℝ))*
        (∫ x, x ∂P.law i) := Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [←Finset.mul_sum]; unfold Instance.totalFirstMoment; ring

end ProphetSecretary.Model
