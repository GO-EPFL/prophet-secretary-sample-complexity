import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Model.Reindex
import ProphetSecretary.Model.ContinuationTransport

/-!
# Partitioning arbitrary retained identities

The original finite identity set is explicitly bijective with its retained
and replaced blocks. The already proved full-policy relabeling transport
preserves the optimal scalar value; values and identities remain observable.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

noncomputable def retainedPartitionMap (A : Finset (Fin N)) : Fin (A.card + Aᶜ.card) → Fin N :=
  Fin.addCases (Model.stateEmbedding A) (Model.stateEmbedding Aᶜ)

lemma retainedPartitionMap_bijective (A : Finset (Fin N)) : Function.Bijective (retainedPartitionMap A) := by
  constructor
  · intro i j heq
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [retainedPartitionMap, Fin.addCases_left] at heq
        exact congrArg (Fin.castAdd Aᶜ.card) ((Model.stateEmbedding A).injective heq)
      | right j =>
        have hi : Model.stateEmbedding A i ∈ A := A.orderEmbOfFin_mem rfl i
        have hj : Model.stateEmbedding Aᶜ j ∈ Aᶜ := Aᶜ.orderEmbOfFin_mem rfl j
        simp only [retainedPartitionMap, Fin.addCases_left, Fin.addCases_right] at heq
        rw [heq] at hi
        exact False.elim ((Finset.mem_compl.mp hj) hi)
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        have hi : Model.stateEmbedding Aᶜ i ∈ Aᶜ := Aᶜ.orderEmbOfFin_mem rfl i
        have hj : Model.stateEmbedding A j ∈ A := A.orderEmbOfFin_mem rfl j
        simp only [retainedPartitionMap, Fin.addCases_left, Fin.addCases_right] at heq
        rw [heq] at hi
        exact False.elim ((Finset.mem_compl.mp hi) hj)
      | right j =>
        simp only [retainedPartitionMap, Fin.addCases_right] at heq
        exact congrArg (Fin.natAdd A.card) ((Model.stateEmbedding Aᶜ).injective heq)
  · intro i
    by_cases hi : i ∈ A
    · refine ⟨(Model.stateIndex A i hi).castAdd Aᶜ.card, ?_⟩
      simp only [retainedPartitionMap, Fin.addCases_left, Model.stateEmbedding_stateIndex]
    · have hic : i ∈ Aᶜ := Finset.mem_compl.mpr hi
      refine ⟨(Model.stateIndex Aᶜ i hic).natAdd A.card, ?_⟩
      simp only [retainedPartitionMap, Fin.addCases_right, Model.stateEmbedding_stateIndex]

noncomputable def retainedPartitionEquiv (A : Finset (Fin N)) : Fin (A.card + Aᶜ.card) ≃ Fin N :=
  Equiv.ofBijective (retainedPartitionMap A) (retainedPartitionMap_bijective A)

lemma retainedPartition_law (P : Model.Instance N) (A : Finset (Fin N)) (i : Fin (A.card + Aᶜ.card)) :
    ((P.restrictTo A).appendIndependent (P.restrictTo Aᶜ)).law i = P.law (retainedPartitionEquiv A i) := by
  induction i using Fin.addCases with
  | left i =>
    simp only [Model.Instance.appendIndependent_law_left]
    change P.law (Model.stateEmbedding A i) = P.law (retainedPartitionMap A (i.castAdd Aᶜ.card))
    rw [retainedPartitionMap, Fin.addCases_left]
  | right j =>
    simp only [Model.Instance.appendIndependent_law_right]
    change P.law (Model.stateEmbedding Aᶜ j) = P.law (retainedPartitionMap A (j.natAdd A.card))
    rw [retainedPartitionMap, Fin.addCases_right]

lemma retainedPartition_value (P : Model.Instance N) (A : Finset (Fin N))
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Model.optimalScalarValue ((P.restrictTo A).appendIndependent (P.restrictTo Aᶜ)) w c =
      Model.optimalScalarValue P w c :=
  P.optimalScalarValue_eq_of_law_equiv _ (retainedPartitionEquiv A) (retainedPartition_law P A) hP hw hc

end ProphetSecretary.Limiting
