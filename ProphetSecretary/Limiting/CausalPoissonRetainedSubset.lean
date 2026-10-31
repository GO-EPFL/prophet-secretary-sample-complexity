import ProphetSecretary.Limiting.CausalPoissonZeroTerminal
import ProphetSecretary.Limiting.RetainedPartition
import ProphetSecretary.Model.StopLossStability

/-!
# Sharp causal Poisson comparison for an arbitrary retained subset

The finite identity partition is explicitly relabeled by a proved bijection.
The retained laws keep the manuscript's original labels through stateEmbedding.
The Poisson intensity is the actual sum of positive restrictions of all replaced
marginals. No finite policy observations are erased in the upper comparison.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {N : ℕ}

noncomputable def poissonizedSubset (P : Model.Instance N) (A : Finset (Fin N)) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) : FiniteIntensityHybridInstance A.card :=
  poissonizedFamily (P.restrictTo A) (P.restrictTo Aᶜ) H
    (fun i => hcap (Model.stateEmbedding A i)) (fun j => hcap (Model.stateEmbedding Aᶜ j))

lemma positiveProbability_eq_capProbability (P : Model.Instance N) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) (i : Fin N) :
    (P.law i).real (Ioi 0) = (P.law i).real (Ioc (0 : ℝ) (H : ℝ)) := by
  have he : (Ioi (0 : ℝ) : Set ℝ) =ᵐ[P.law i] Ioc (0 : ℝ) (H : ℝ) := by
    filter_upwards [hcap i] with x hx
    apply propext
    exact ⟨fun h => ⟨h,hx⟩, fun h => h.1⟩
  exact congrArg ENNReal.toReal (measure_congr he)

lemma positiveMarginal_capProbability (P : Model.Instance N) (H : ℝ≥0) (i : Fin N) :
    (positiveOfferMarginal P i : Measure ℝ) (Ioc (0 : ℝ) (H : ℝ)) =
      P.law i (Ioc (0 : ℝ) (H : ℝ)) := by
  change ((P.law i).restrict (Ioi 0)) (Ioc (0 : ℝ) (H : ℝ)) = _
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]

/-- The zero-terminal specialization of `lem:causal-poisson`, with its full
arbitrary-retained-subset quantifier and manuscript pᵢ=νᵢ((0,H]) coefficient. -/
theorem causalPoisson_retainedSubset_zeroTerminal (P : Model.Instance N) (A : Finset (Fin N)) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalScalarValue P w c - (poissonizedSubset P A H hcap).optimalScalarValue w c| ≤
      (Real.pi / 2) * w * (H : ℝ) *
        Real.sqrt (∑ i ∈ Aᶜ, ((P.law i).real (Ioc (0 : ℝ) (H : ℝ))) ^ 2) := by
  have h := causalPoisson_zeroTerminal (P.restrictTo A) (P.restrictTo Aᶜ) H
    (fun i => hcap (Model.stateEmbedding A i)) (fun j => hcap (Model.stateEmbedding Aᶜ j)) hw hc
  rw [retainedPartition_value P A (P.integrable_maximum_of_bounded hcap) hw hc] at h
  have hsum : (∑ j, distributionTail (P.restrictTo Aᶜ) 0 j ^ 2) =
      ∑ i ∈ Aᶜ, ((P.law i).real (Ioi 0)) ^ 2 := by
    change (∑ j, ((P.law (Model.stateEmbedding Aᶜ j)).real (Ioi 0)) ^ 2) = _
    exact Model.sum_stateEmbedding Aᶜ (fun i => ((P.law i).real (Ioi 0)) ^ 2)
  rw [hsum] at h
  simp_rw [positiveProbability_eq_capProbability P H hcap] at h
  exact h

end ProphetSecretary.Limiting
