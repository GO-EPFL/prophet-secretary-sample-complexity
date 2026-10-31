import ProphetSecretary.Limiting.CausalPoissonReserve
import ProphetSecretary.Limiting.CausalPoissonRetainedSubset
import ProphetSecretary.Model.TerminalReindex

/-!
# Sharp causal Poisson replacement

This is `lem:causal-poisson` for any finite independent bounded instance, any
chosen retained identity subset, and the same fixed terminal reward in both
models. The π/2 coefficient is independent of the instance size. The finite
upper comparison includes every original observed zero identity and all
admissible independent policy randomness.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {N : ℕ}

noncomputable def poissonizedSubsetTerminal (P : Model.Instance N) (A : Finset (Fin N)) (H a : ℝ≥0)
    (haH : a ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) : FiniteIntensityHybridInstance A.card :=
  poissonizedFamilyTerminal (P.restrictTo A) (P.restrictTo Aᶜ) H a haH
    (fun i => hcap (Model.stateEmbedding A i)) (fun j => hcap (Model.stateEmbedding Aᶜ j))

/-- `lem:causal-poisson`. Here pᵢ is exactly νᵢ((0,H]), where νᵢ is the actual
positive marginal restriction; the coefficient therefore matches the paper. -/
theorem causalPoisson_comparison (P : Model.Instance N) (A : Finset (Fin N)) (H a : ℝ≥0)
    (haH : a ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalTerminalScalarValue P a w c - (poissonizedSubsetTerminal P A H a haH hcap).optimalScalarValue w c| ≤
      (Real.pi / 2) * w * (H : ℝ) *
        Real.sqrt (∑ i ∈ Aᶜ, ((P.law i).real (Ioc (0 : ℝ) (H : ℝ))) ^ 2) := by
  let B := poissonizedSubsetTerminal P A H a haH hcap
  have h := causalPoisson_fixedTerminal (P.restrictTo A) (P.restrictTo Aᶜ) H a haH
    (fun i => hcap (Model.stateEmbedding A i)) (fun j => hcap (Model.stateEmbedding Aᶜ j)) hw hc
  have hv := P.optimalTerminalScalarValue_eq_of_law_equiv
    ((P.restrictTo A).appendIndependent (P.restrictTo Aᶜ)) (retainedPartitionEquiv A) (retainedPartition_law P A)
      (P.integrable_maximum_of_bounded hcap) a.property hw hc
  have hsum : (∑ j, distributionTail (P.restrictTo Aᶜ) 0 j ^ 2) =
      ∑ i ∈ Aᶜ, ((P.law i).real (Ioi 0)) ^ 2 := by
    change (∑ j, ((P.law (Model.stateEmbedding Aᶜ j)).real (Ioi 0)) ^ 2) = _
    exact Model.sum_stateEmbedding Aᶜ (fun i => ((P.law i).real (Ioi 0)) ^ 2)
  rw [hsum] at h
  simp_rw [positiveProbability_eq_capProbability P H hcap] at h
  have hdiff : Model.optimalTerminalScalarValue ((P.restrictTo A).appendIndependent (P.restrictTo Aᶜ)) a w c -
      B.optimalScalarValue w c = Model.optimalTerminalScalarValue P a w c - B.optimalScalarValue w c :=
    congrArg (fun x : ℝ => x - B.optimalScalarValue w c) hv
  change |Model.optimalTerminalScalarValue P a w c - B.optimalScalarValue w c| ≤ _
  exact (congrArg abs hdiff).symm.le.trans h

end ProphetSecretary.Limiting
