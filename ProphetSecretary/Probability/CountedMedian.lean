import ProphetSecretary.Probability.FiniteOrderStatistic
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# An executable median with a hard quadratic work bound

Insertion sort retains repeated observations. Work counts comparisons and
list-construction steps; median extraction and forming the input list are
included in the final bound. The powerset formula for order statistics is
used only to prove mathematical correspondence.
-/

namespace ProphetSecretary.Probability

open scoped BigOperators

def countedOrderedInsert {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (a : α) : List α → List α × ℕ
  | [] => ([a], 1)
  | b :: l => if r a b then (a :: b :: l, 3) else
      let q := countedOrderedInsert r a l
      (b :: q.1, q.2 + 2)

lemma countedOrderedInsert_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (a : α) (l : List α) : (countedOrderedInsert r a l).1 = List.orderedInsert r a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : r a b <;> simp [countedOrderedInsert, List.orderedInsert, h, ih]

lemma countedOrderedInsert_work {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (a : α) (l : List α) : (countedOrderedInsert r a l).2 ≤ 3 * (l.length + 1) := by
  induction l with
  | nil => norm_num [countedOrderedInsert]
  | cons b l ih =>
    by_cases h : r a b <;> simp only [countedOrderedInsert, h, ↓reduceIte, List.length_cons]
    · omega
    · omega

def countedInsertionSort {α : Type*} (r : α → α → Prop) [DecidableRel r] : List α → List α × ℕ
  | [] => ([], 1)
  | a :: l =>
      let q := countedInsertionSort r l
      let s := countedOrderedInsert r a q.1
      (s.1, q.2 + s.2 + 1)

lemma countedInsertionSort_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (l : List α) : (countedInsertionSort r l).1 = List.insertionSort r l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [countedInsertionSort, countedOrderedInsert_value, ih, List.insertionSort_cons]

lemma countedInsertionSort_work {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (l : List α) : (countedInsertionSort r l).2 ≤ 4 * (l.length + 1) ^ 2 := by
  induction l with
  | nil => norm_num [countedInsertionSort]
  | cons a l ih =>
    have hInsert := countedOrderedInsert_work r a (countedInsertionSort r l).1
    have hLen : (countedInsertionSort r l).1.length = l.length := by
      rw [countedInsertionSort_value, List.length_insertionSort]
    rw [hLen] at hInsert
    simp only [countedInsertionSort, List.length_cons]
    nlinarith

def sortedMedian {α : Type*} [LinearOrder α] (k : ℕ) (x : Fin (2 * k + 1) → α) : α :=
  (List.insertionSort (fun a b => b ≤ a) (List.ofFn x)).get
    ⟨k, by simp only [List.length_insertionSort, List.length_ofFn]; omega⟩

def countedMedian {α : Type*} [LinearOrder α] (k : ℕ) (x : Fin (2 * k + 1) → α) : α × ℕ :=
  let q := countedInsertionSort (fun a b => b ≤ a) (List.ofFn x)
  (q.1.get ⟨k, by rw [countedInsertionSort_value, List.length_insertionSort, List.length_ofFn]; omega⟩,
    q.2 + 3 * (2 * k + 1) + 1)

lemma countedMedian_value {α : Type*} [LinearOrder α] (k : ℕ) (x : Fin (2 * k + 1) → α) :
    (countedMedian k x).1 = sortedMedian k x := by
  dsimp only [countedMedian, sortedMedian]
  have hv := countedInsertionSort_value (fun a b : α => b ≤ a) (List.ofFn x)
  have hl : k < (countedInsertionSort (fun a b : α => b ≤ a) (List.ofFn x)).1.length := by
    rw [hv, List.length_insertionSort, List.length_ofFn]
    omega
  have hr : k < (List.insertionSort (fun a b : α => b ≤ a) (List.ofFn x)).length := by
    simp only [List.length_insertionSort, List.length_ofFn]
    omega
  have he := congrArg (fun l : List α => l[k]?) hv
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hr] at he
  exact Option.some.inj he

lemma countedMedian_work {α : Type*} [LinearOrder α] (k : ℕ) (x : Fin (2 * k + 1) → α) :
    (countedMedian k x).2 ≤ 8 * (2 * k + 1 + 1) ^ 2 := by
  have h := countedInsertionSort_work (fun a b : α => b ≤ a) (List.ofFn x)
  simp only [List.length_ofFn] at h
  dsimp only [countedMedian]
  nlinarith

lemma countP_ofFn_eq_card {α : Type*} {n : ℕ} (x : Fin n → α)
    (p : α → Prop) [DecidablePred p] :
    (List.ofFn x).countP (fun a => decide (p a)) = (Finset.univ.filter (fun i => p (x i))).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.card_filter_univ_succ']
    rw [ih]
    by_cases h : p (x 0) <;> simp [h, Nat.add_comm]

lemma le_sorted_get_iff_countP {α : Type*} [LinearOrder α] (l : List α) (hl : l.SortedGE)
    (j : Fin l.length) (c : α) :
    c ≤ l.get j ↔ j.val + 1 ≤ l.countP (fun a => decide (c ≤ a)) := by
  have hc : l.countP (fun a => decide (c ≤ a)) =
      (Finset.univ.filter (fun i : Fin l.length => c ≤ l.get i)).card := by
    simpa only [List.ofFn_get] using countP_ofFn_eq_card l.get (fun a => c ≤ a)
  have h := Fin.lt_card_filter_univ_iff_apply_of_imp (j := j)
    (fun i : Fin l.length => c ≤ l.get i)
    (fun i q hqi hi => hi.trans (hl.antitone_get hqi))
  rw [← hc] at h
  simpa only [Nat.lt_iff_add_one_le] using h.symm

lemma le_sortedMedian_iff {α : Type*} [LinearOrder α] (k : ℕ)
    (x : Fin (2 * k + 1) → α) (c : α) :
    c ≤ sortedMedian k x ↔ k + 1 ≤ (Finset.univ.filter (fun i => c ≤ x i)).card := by
  let l := List.insertionSort (fun a b => b ≤ a) (List.ofFn x)
  have hl : l.SortedGE := (List.pairwise_insertionSort (fun a b : α => b ≤ a) _).sortedGE
  have hj : k < l.length := by simp only [l, List.length_insertionSort, List.length_ofFn]; omega
  have h := le_sorted_get_iff_countP l hl ⟨k, hj⟩ c
  have hp := (List.perm_insertionSort (fun a b : α => b ≤ a) (List.ofFn x)).countP_eq
    (fun a => decide (c ≤ a))
  rw [hp, countP_ofFn_eq_card] at h
  exact h

lemma sortedMedian_eq_sampleOrderStatistic {α : Type*} [LinearOrder α] (k : ℕ)
    (x : Fin (2 * k + 1) → α) :
    sortedMedian k x = sampleOrderStatistic (k + 1) (by omega) (by simp; omega) x := by
  apply le_antisymm
  · apply (le_sampleOrderStatistic_iff (k + 1) (by omega) (by simp; omega) x _).2
    exact (le_sortedMedian_iff k x _).1 le_rfl
  · apply (le_sortedMedian_iff k x _).2
    exact (le_sampleOrderStatistic_iff (k + 1) (by omega) (by simp; omega) x _).1 le_rfl

structure MedianCopiesResult (α : Type*) where
  value : α
  work : ℕ
  copies : ℕ

/-- Each call is evaluated once when the output list is formed; the stored
values and costs are subsequently projected without rerunning the calls. -/
def countedMedianCopies {α Seed : Type*} [LinearOrder α] (k : ℕ)
    (call : Seed → α × ℕ) (seed : Fin (2 * k + 1) → Seed) : MedianCopiesResult α :=
  let outputs := List.ofFn (fun i => call (seed i))
  let values := outputs.map Prod.fst
  let q := countedInsertionSort (fun a b => b ≤ a) values
  { value := q.1.get ⟨k, by
      rw [countedInsertionSort_value, List.length_insertionSort,
        List.length_map, List.length_ofFn]
      omega⟩
    work := (outputs.map Prod.snd).sum + q.2 + 8 * (2 * k + 1) + 1
    copies := outputs.length }

lemma countedMedianCopies_value {α Seed : Type*} [LinearOrder α] (k : ℕ)
    (call : Seed → α × ℕ) (seed : Fin (2 * k + 1) → Seed) :
    (countedMedianCopies k call seed).value = sortedMedian k (fun i => (call (seed i)).1) := by
  let values := (List.ofFn (fun i => call (seed i))).map Prod.fst
  have hvalues : values = List.ofFn (fun i => (call (seed i)).1) := by
    simp [values, List.map_ofFn, Function.comp_def]
  have hv : (countedInsertionSort (fun a b : α => b ≤ a) values).1 =
      List.insertionSort (fun a b => b ≤ a) (List.ofFn (fun i => (call (seed i)).1)) := by
    rw [countedInsertionSort_value, hvalues]
  have hl : k < (countedInsertionSort (fun a b : α => b ≤ a) values).1.length := by
    rw [hv, List.length_insertionSort, List.length_ofFn]
    omega
  have hr : k < (List.insertionSort (fun a b : α => b ≤ a)
      (List.ofFn (fun i => (call (seed i)).1))).length := by
    simp only [List.length_insertionSort, List.length_ofFn]
    omega
  have he := congrArg (fun l : List α => l[k]?) hv
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hr] at he
  exact Option.some.inj he

lemma countedMedianCopies_copies {α Seed : Type*} [LinearOrder α] (k : ℕ)
    (call : Seed → α × ℕ) (seed : Fin (2 * k + 1) → Seed) :
    (countedMedianCopies k call seed).copies = 2 * k + 1 := by
  simp [countedMedianCopies]

lemma countedMedianCopies_work {α Seed : Type*} [LinearOrder α] (k : ℕ)
    (call : Seed → α × ℕ) (seed : Fin (2 * k + 1) → Seed) (W : ℕ)
    (hW : ∀ s, (call s).2 ≤ W) :
    (countedMedianCopies k call seed).work ≤ (2 * k + 1) * W + 8 * (2 * k + 1 + 1) ^ 2 := by
  have hsum : ((List.ofFn (fun i => call (seed i))).map Prod.snd).sum ≤ (2 * k + 1) * W := by
    rw [List.map_ofFn, Fin.sum_ofFn]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hW (seed i))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Function.comp_def, Nat.cast_id] using h
  have hs := countedInsertionSort_work (fun a b : α => b ≤ a)
    ((List.ofFn (fun i => call (seed i))).map Prod.fst)
  simp only [List.length_map, List.length_ofFn] at hs
  dsimp only [countedMedianCopies]
  nlinarith

end ProphetSecretary.Probability
