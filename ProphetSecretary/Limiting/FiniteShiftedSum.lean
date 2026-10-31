import ProphetSecretary.Limiting.WeightedPaddedInstance
import ProphetSecretary.Limiting.ContinuousWeightedBandExtraction

/-!
# Shifted finite tails with zero padding

These identities retain the actual finite variable indices while allowing a
fixed retained-prefix size larger than the original instance size.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

lemma shifted_finite_sum_eq_filtered {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (n N : ℕ) (hf : ∀ j, n ≤ j → f j = 0) :
    (∑ j ∈ Finset.range n, f (N+j)) = ∑ j ∈ (Finset.range n).filter (fun j => N ≤ j), f j := by
  have h := Finset.sum_Ico_eq_sum_range f N (N+n)
  simp only [Nat.add_sub_cancel_left] at h
  rw [← h]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro j hj
    have h := Finset.mem_filter.mp hj
    exact Finset.mem_Ico.mpr ⟨h.2,(Finset.mem_range.mp h.1).trans_le (Nat.le_add_left n N)⟩
  · intro j hj
    have hmem := Finset.mem_sdiff.mp hj
    have hnot := hmem.2
    have hjI := Finset.mem_Ico.mp hmem.1
    apply hf
    by_contra hn
    have hlt : j < n := not_le.mp hn
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hjI.1⟩)
  · intro _ _
    rfl

lemma shifted_fin_sum_eq_filtered {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (n N : ℕ) (hf : ∀ j, n ≤ j → f j = 0) :
    (∑ i : Fin n, f (N+i.val)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val), f i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (N+j)) n,
    shifted_finite_sum_eq_filtered f n N hf,Finset.sum_filter,Finset.sum_filter]
  exact (Fin.sum_univ_eq_sum_range (fun j => if N ≤ j then f j else 0) n).symm

end ProphetSecretary.Limiting
