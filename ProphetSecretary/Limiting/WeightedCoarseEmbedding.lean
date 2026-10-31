import ProphetSecretary.Limiting.WeightedPaddedInstance
import ProphetSecretary.Limiting.IndividualGapIndex

/-!
# Retained-prefix and residual identities in an ordered padded instance

The static identity injection keeps the first K offers and the shifted
residual block beginning at N. Intermediate identities are ignored by a
causal policy projection; no choice depends on offer values or arrival times.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting

noncomputable def weightedCoarseEmbedding (n K N : ℕ) (hKN : K ≤ N) : Fin (K+n) ↪ Fin (n+N) :=
  (HybridZeroSimulation.keepEmbedding K (N-K) n).toEmbedding.trans
    (finCongr (show K+(N-K)+n=n+N by omega)).toEmbedding

lemma weightedCoarseEmbedding_left (n K N : ℕ) (hKN : K ≤ N) (i : Fin K) :
    (weightedCoarseEmbedding n K N hKN (i.castAdd n)).val=i.val := by
  change (HybridZeroSimulation.keepEmbedding K (N-K) n (i.castAdd n)).val=i.val
  rw [HybridZeroSimulation.keepEmbedding_left]
  rfl

lemma weightedCoarseEmbedding_right (n K N : ℕ) (hKN : K ≤ N) (j : Fin n) :
    (weightedCoarseEmbedding n K N hKN (j.natAdd K)).val=N+j.val := by
  change (HybridZeroSimulation.keepEmbedding K (N-K) n (j.natAdd K)).val=N+j.val
  rw [HybridZeroSimulation.keepEmbedding_right]
  simp only [Fin.val_natAdd]
  omega

lemma weightedCoarse_restricted_instance {n : ℕ} (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (K N : ℕ) (hKN : K ≤ N) :
    (((P.restrictBy (weightedMeanPermutation P w).toEmbedding).appendZeros N).restrictBy
      (weightedCoarseEmbedding n K N hKN))=
      (weightOrderedPrefix P w K).appendIndependent (weightOrderedRemainder P w N) := by
  apply Model.Instance.eq_of_law_eq
  funext k
  change ((P.restrictBy (weightedMeanPermutation P w).toEmbedding).appendZeros N).law
    (weightedCoarseEmbedding n K N hKN k)=_
  rw [weightOrderedPrefix_full_law P w N]
  induction k using Fin.addCases with
  | left i =>
    simp only [weightOrderedPrefix,Model.Instance.appendIndependent,Fin.addCases_left]
    exact congrArg (fun j : ℕ => (weightOrderedPaddedLaw P w j:Measure ℝ))
      (weightedCoarseEmbedding_left n K N hKN i)
  | right j =>
    simp only [weightOrderedPrefix,Model.Instance.appendIndependent,Fin.addCases_right,weightOrderedRemainder]
    exact congrArg (fun k : ℕ => (weightOrderedPaddedLaw P w k:Measure ℝ))
      (weightedCoarseEmbedding_right n K N hKN j)

end ProphetSecretary.Limiting
