import ProphetSecretary.Limiting.ClosureCompensatedIntensityFinite
import ProphetSecretary.Limiting.ResidualPayloadDecomposition

/-!
# Positive prefix decomposition of the compensated residual array

The segment between a fixed retained prefix and the slowly growing tilted
prefix is unchanged. The remainder is exactly the compensated diagonal.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting

lemma compensatedResidualOffers_residual_decomposition {n : ℕ} (P : Model.Instance n)
    {N M : ℕ} (hNM : N≤M) (c : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (θ : ℝ) (hθ : |θ|≤1/4) :
    labeledBandResidual (compensatedResidualOffers P M S hS θ hθ) N c=
      residualPayloadBase P N M c c+
        labeledBandResidual (compensatedResidualOffers P M S hS θ hθ) M c := by
  unfold labeledBandResidual residualPayloadBase
  rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hNj : N≤j.val
  · rw [if_pos hNj,if_pos hNj]
    by_cases hMj : M≤j.val
    · rw [if_pos hMj,if_neg (not_lt.mpr hMj)]
      have hEmpty : (P.marginalProbabilityLaw j).toFiniteMeasure.restrict (∅ : Set ℝ)=0 := by
        apply FiniteMeasure.toMeasure_injective
        rw [FiniteMeasure.restrict_measure_eq,Measure.restrict_empty]
        rfl
      rw [Ioc_self,hEmpty,zero_add]
    · rw [if_neg hMj,if_pos (not_le.mp hMj),add_zero]
      congr 1
      apply FiniteMeasure.toMeasure_injective
      exact compensatedResidualOffers_law_before P M hS θ hθ j (not_le.mp hMj)
  · have hMj : ¬M≤j.val := fun hj => hNj (hNM.trans hj)
    rw [if_neg hNj,if_neg hNj,if_neg hMj,zero_add]

end ProphetSecretary.Limiting
