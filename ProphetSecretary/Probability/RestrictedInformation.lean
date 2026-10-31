import ProphetSecretary.Model.Continuation
import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Information retained by an unseen subset

The sorted child keeps exactly the original marginal score of each retained
identity. Nonnegative second moments therefore sum to at most the full product
score information, without a cardinality relaxation.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

lemma information_restrictTo_le (P : Instance n) (A : Finset (Fin n)) (s : Fin n → ℝ → ℝ) :
    information (P.restrictTo A).law (fun j ↦ s (stateEmbedding A j)) ≤ information P.law s := by
  unfold information
  change (∑ j : Fin A.card, ∫ a, s (stateEmbedding A j) a ^ 2 ∂P.law (stateEmbedding A j)) ≤ _
  let f := fun i : Fin n ↦ ∫ a, s i a ^ 2 ∂P.law i
  have he : (∑ j : Fin A.card, f (stateEmbedding A j)) =
      ∑ i ∈ (Finset.univ : Finset (Fin A.card)).map (stateEmbedding A), f i := by rw [Finset.sum_map]
  change (∑ j : Fin A.card, f (stateEmbedding A j)) ≤ ∑ i : Fin n, f i
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ integral_nonneg (fun a ↦ sq_nonneg (s i a)))

end ProphetSecretary.Model.Instance
