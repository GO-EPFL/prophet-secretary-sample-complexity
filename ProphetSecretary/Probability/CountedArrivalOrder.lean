import ProphetSecretary.Model.ArrivalRepresentation
import ProphetSecretary.Probability.CountedOrderStatistic

/-!
# Sorting independent clocks for the arithmetic execution

The forward and inverse order are stored as vectors, so rank and identity
lookups during validation do not repeat list searches. Ties are broken by
identity; continuous uniforms have no ties almost surely.
-/

namespace ProphetSecretary.Probability
open ProphetSecretary.Model

variable {n : ℕ} {K : Type} [LinearOrder K]

private lemma vector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

def vectorPermutation (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  let a := Vector.ofFn p
  let b := Vector.ofFn p.symm
  ⟨a.get,b.get,by intro i; simp only [a,b,vector_get_ofFn,Equiv.symm_apply_apply],
    by intro i; simp only [a,b,vector_get_ofFn,Equiv.apply_symm_apply]⟩

lemma vectorPermutation_eq (p : Equiv.Perm (Fin n)) : vectorPermutation p=p := by
  apply Equiv.ext
  intro i
  exact vector_get_ofFn p i

def countedArrivalOrder (u : Fin n → K) : Equiv.Perm (Fin n) × ℕ :=
  let r := fun i j => toLex (u i,i) ≤ toLex (u j,j)
  let q := countedInsertionSort r (List.finRange n)
  have hp : List.Perm q.1 (List.finRange n) := by
    rw [countedInsertionSort_value]
    exact List.perm_insertionSort _ _
  have hlen : q.1.length=n := hp.length_eq.trans List.length_finRange
  let e := (finCongr hlen.symm).trans (List.Nodup.getEquivOfForallMemList q.1
    (hp.nodup_iff.mpr (List.nodup_finRange n)) (fun i => hp.mem_iff.mpr (List.mem_finRange i)))
  (vectorPermutation e,q.2+6*(n+1)^2)

lemma countedArrivalOrder_work (u : Fin n → K) :
    (countedArrivalOrder u).2≤10*(n+1)^2 := by
  have h := countedInsertionSort_work (fun i j => toLex (u i,i) ≤ toLex (u j,j)) (List.finRange n)
  simp only [List.length_finRange] at h
  unfold countedArrivalOrder
  dsimp only
  omega

lemma countedArrivalOrder_monotone (u : Fin n → K) :
    Monotone (fun i => u ((countedArrivalOrder u).1 i)) := by
  let r := fun i j => toLex (u i,i) ≤ toLex (u j,j)
  let q := countedInsertionSort r (List.finRange n)
  have hs : q.1.Pairwise r := by
    rw [countedInsertionSort_value]
    apply List.pairwise_insertionSort
  have hl : q.1.length=n := by rw [countedInsertionSort_value,List.length_insertionSort,List.length_finRange]
  apply monotone_iff_forall_lt.mpr
  intro i j hij
  have hi : i.val<q.1.length := hl.symm ▸ i.isLt
  have hj : j.val<q.1.length := hl.symm ▸ j.isLt
  have h := List.pairwise_iff_getElem.mp hs i.val j.val hi hj hij
  simp only [countedArrivalOrder,vectorPermutation_eq]
  change u q.1[i.val] ≤ u q.1[j.val]
  exact (Prod.Lex.le_iff.mp h).elim le_of_lt (fun h => h.1.le)

omit [LinearOrder K] in
lemma countedArrivalOrder_eq {u : Fin n → ℝ} (hu : Function.Injective u) :
    (countedArrivalOrder u).1=Instance.arrivalPermutation u := by
  symm
  apply (Instance.arrivalPermutation_eq_iff hu _).2
  intro i j hij
  exact lt_of_le_of_ne (countedArrivalOrder_monotone u hij.le)
    (fun h => hij.ne (((countedArrivalOrder u).1.injective) (hu h)))

end ProphetSecretary.Probability
