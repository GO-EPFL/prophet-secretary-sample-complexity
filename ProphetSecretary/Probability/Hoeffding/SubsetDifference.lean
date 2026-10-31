import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic

/-!
# Alternating finite-subset differences

This is the finite inclusion-exclusion identity behind the Hoeffding
components. Summing all alternating subset differences recovers the original
set-indexed quantity. Invariance under adding one coordinate makes its
alternating difference vanish.
-/
open scoped BigOperators Classical
namespace ProphetSecretary.Probability.Hoeffding
variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

noncomputable def subsetDifference (h : Finset ι → E) (A : Finset ι) : E :=
  ∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card) • h B

omit [DecidableEq ι] in
lemma subsetDifference_empty (h : Finset ι → E) : subsetDifference h ∅ = h ∅ := by
  simp [subsetDifference]

lemma subsetDifference_insert (h : Finset ι → E) (A : Finset ι) {i : ι} (hi : i ∉ A) :
    subsetDifference h (insert i A) = subsetDifference (fun B => h (insert i B)) A-subsetDifference h A := by
  unfold subsetDifference
  rw [Finset.sum_powerset_insert hi,Finset.card_insert_of_notMem hi]
  have hfirst : (∑ B ∈ A.powerset, (-1 : ℝ)^(A.card+1-B.card) • h B) =
      -(∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card) • h B) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro B hB
    have hBA := Finset.card_le_card (Finset.mem_powerset.mp hB)
    have he : A.card+1-B.card = (A.card-B.card)+1 := by omega
    rw [he]
    simp [pow_succ]
  have hsecond : (∑ B ∈ A.powerset, (-1 : ℝ)^(A.card+1-(insert i B).card) • h (insert i B)) =
      ∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card) • h (insert i B) := by
    apply Finset.sum_congr rfl
    intro B hB
    have hiB : i ∉ B := fun h => hi (Finset.mem_powerset.mp hB h)
    rw [Finset.card_insert_of_notMem hiB,Nat.add_sub_add_right]
  rw [hfirst,hsecond]
  abel

/-- Finite subset inversion, proved for arbitrary module-valued quantities. -/
lemma sum_subsetDifference (h : Finset ι → E) (A : Finset ι) :
    (∑ B ∈ A.powerset, subsetDifference h B) = h A := by
  induction A using Finset.induction_on generalizing h with
  | empty => simp [subsetDifference_empty]
  | @insert i A hi ih =>
    rw [Finset.sum_powerset_insert hi]
    have he (B : Finset ι) (hB : B ∈ A.powerset) :
        subsetDifference h (insert i B) = subsetDifference (fun C => h (insert i C)) B-subsetDifference h B :=
      subsetDifference_insert h B (fun hBi => hi (Finset.mem_powerset.mp hB hBi))
    rw [Finset.sum_congr rfl he,Finset.sum_sub_distrib,ih,ih]
    abel

lemma subsetDifference_eq_zero_of_insert_invariant (h : Finset ι → E) (A : Finset ι)
    {i : ι} (hi : i ∈ A) (hinv : ∀ B ⊆ A.erase i, h (insert i B) = h B) :
    subsetDifference h A = 0 := by
  have he : A = insert i (A.erase i) := (Finset.insert_erase hi).symm
  rw [he,subsetDifference_insert h (A.erase i) (Finset.notMem_erase i A)]
  have hs : subsetDifference (fun B => h (insert i B)) (A.erase i) = subsetDifference h (A.erase i) := by
    unfold subsetDifference
    apply Finset.sum_congr rfl
    intro B hB
    dsimp only
    rw [hinv B (Finset.mem_powerset.mp hB)]
  rw [hs,sub_self]

end ProphetSecretary.Probability.Hoeffding
