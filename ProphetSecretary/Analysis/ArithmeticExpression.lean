import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Arithmetic expression work

Each integer constant or input read costs one unit. Binary arithmetic and
minimum/maximum nodes add one primitive operation to the work of their
operands. Evaluation over rationals and reals has the same expression tree.
-/

namespace ProphetSecretary.Analysis

inductive ArithmeticExpression (ι : Type*) where
  | integer : ℤ → ArithmeticExpression ι
  | input : ι → ArithmeticExpression ι
  | add : ArithmeticExpression ι → ArithmeticExpression ι → ArithmeticExpression ι
  | sub : ArithmeticExpression ι → ArithmeticExpression ι → ArithmeticExpression ι
  | mul : ArithmeticExpression ι → ArithmeticExpression ι → ArithmeticExpression ι
  | div : ArithmeticExpression ι → ArithmeticExpression ι → ArithmeticExpression ι
  | minimum : ArithmeticExpression ι → ArithmeticExpression ι → ArithmeticExpression ι
  | maximum : ArithmeticExpression ι → ArithmeticExpression ι → ArithmeticExpression ι
  deriving Repr

namespace ArithmeticExpression

variable {ι κ K : Type*}

def eval [Field K] [LinearOrder K] (x : ι → K) : ArithmeticExpression ι → K
  | .integer z => z
  | .input i => x i
  | .add a b => eval x a + eval x b
  | .sub a b => eval x a - eval x b
  | .mul a b => eval x a * eval x b
  | .div a b => eval x a / eval x b
  | .minimum a b => min (eval x a) (eval x b)
  | .maximum a b => max (eval x a) (eval x b)

def work : ArithmeticExpression ι → ℕ
  | .integer _ | .input _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => work a + work b + 1

def map (f : ι → κ) : ArithmeticExpression ι → ArithmeticExpression κ
  | .integer z => .integer z
  | .input i => .input (f i)
  | .add a b => .add (map f a) (map f b)
  | .sub a b => .sub (map f a) (map f b)
  | .mul a b => .mul (map f a) (map f b)
  | .div a b => .div (map f a) (map f b)
  | .minimum a b => .minimum (map f a) (map f b)
  | .maximum a b => .maximum (map f a) (map f b)

@[simp] lemma eval_map [Field K] [LinearOrder K] (f : ι → κ) (x : κ → K) (e : ArithmeticExpression ι) :
    eval x (map f e) = eval (fun i => x (f i)) e := by
  induction e <;> simp_all [map, eval]

@[simp] lemma work_map (f : ι → κ) (e : ArithmeticExpression ι) : work (map f e) = work e := by
  induction e <;> simp_all [map, work]

lemma eval_ratCast (x : ι → ℚ) (e : ArithmeticExpression ι) :
    ((eval x e : ℚ) : ℝ) = eval (fun i => (x i : ℝ)) e := by
  induction e <;> simp_all [eval]

def sumList {α : Type*} (l : List α) (f : α → ArithmeticExpression ι) : ArithmeticExpression ι :=
  l.foldr (fun i e => .add (f i) e) (.integer 0)

def productList {α : Type*} (l : List α) (f : α → ArithmeticExpression ι) : ArithmeticExpression ι :=
  l.foldr (fun i e => .mul (f i) e) (.integer 1)

def maximumList {α : Type*} (l : List α) (f : α → ArithmeticExpression ι) : ArithmeticExpression ι :=
  l.foldr (fun i e => .maximum (f i) e) (.integer 0)

@[simp] lemma eval_sumList [Field K] [LinearOrder K] {α : Type*}
    (x : ι → K) (l : List α) (f : α → ArithmeticExpression ι) :
    eval x (sumList l f) = (l.map (fun i => eval x (f i))).sum := by
  induction l <;> simp_all [sumList, eval]

@[simp] lemma eval_productList [Field K] [LinearOrder K] {α : Type*}
    (x : ι → K) (l : List α) (f : α → ArithmeticExpression ι) :
    eval x (productList l f) = (l.map (fun i => eval x (f i))).prod := by
  induction l <;> simp_all [productList, eval]

lemma work_sumList_le {α : Type*} (l : List α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ l, work (f i) ≤ B) : work (sumList l f) ≤ 1 + l.length * (B + 1) := by
  induction l with
  | nil => simp [sumList, work]
  | cons i l ih =>
    have hi := h i (List.mem_cons_self)
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [sumList, List.foldr_cons, work, List.length_cons]
    calc
      work (f i) + work (sumList l f) + 1 ≤ B + (1 + l.length * (B + 1)) + 1 := by omega
      _ = 1 + (l.length + 1) * (B + 1) := by ring

lemma work_productList_le {α : Type*} (l : List α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ l, work (f i) ≤ B) : work (productList l f) ≤ 1 + l.length * (B + 1) := by
  induction l with
  | nil => simp [productList, work]
  | cons i l ih =>
    have hi := h i (List.mem_cons_self)
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [productList, List.foldr_cons, work, List.length_cons]
    calc
      work (f i) + work (productList l f) + 1 ≤ B + (1 + l.length * (B + 1)) + 1 := by omega
      _ = 1 + (l.length + 1) * (B + 1) := by ring

lemma work_maximumList_le {α : Type*} (l : List α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ l, work (f i) ≤ B) : work (maximumList l f) ≤ 1 + l.length * (B + 1) := by
  induction l with
  | nil => simp [maximumList, work]
  | cons i l ih =>
    have hi := h i (List.mem_cons_self)
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [maximumList, List.foldr_cons, work, List.length_cons]
    calc
      work (f i) + work (maximumList l f) + 1 ≤ B + (1 + l.length * (B + 1)) + 1 := by omega
      _ = 1 + (l.length + 1) * (B + 1) := by ring

def sumFinset {α : Type*} [LinearOrder α] (A : Finset α) (f : α → ArithmeticExpression ι) : ArithmeticExpression ι :=
  sumList (A.sort (· ≤ ·)) f

def productFinset {α : Type*} [LinearOrder α] (A : Finset α) (f : α → ArithmeticExpression ι) : ArithmeticExpression ι :=
  productList (A.sort (· ≤ ·)) f

@[simp] lemma eval_sumFinset [Field K] [LinearOrder K] {α : Type*} [LinearOrder α]
    (x : ι → K) (A : Finset α) (f : α → ArithmeticExpression ι) :
    eval x (sumFinset A f) = ∑ i ∈ A, eval x (f i) := by
  rw [sumFinset, eval_sumList]
  exact ((A.sort_perm_toList (· ≤ ·)).map (fun i => eval x (f i))).sum_eq.trans
    (Finset.sum_map_toList A _)

@[simp] lemma eval_productFinset [Field K] [LinearOrder K] {α : Type*} [LinearOrder α]
    (x : ι → K) (A : Finset α) (f : α → ArithmeticExpression ι) :
    eval x (productFinset A f) = ∏ i ∈ A, eval x (f i) := by
  rw [productFinset, eval_productList]
  exact ((A.sort_perm_toList (· ≤ ·)).map (fun i => eval x (f i))).prod_eq.trans
    (Finset.prod_map_toList A _)

lemma work_sumFinset_le {α : Type*} [LinearOrder α] (A : Finset α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ A, work (f i) ≤ B) : work (sumFinset A f) ≤ 1 + A.card * (B + 1) := by
  simpa only [sumFinset, Finset.length_sort] using
    work_sumList_le (A.sort (· ≤ ·)) f B (fun i hi => h i ((A.mem_sort (· ≤ ·)).mp hi))

lemma work_productFinset_le {α : Type*} [LinearOrder α] (A : Finset α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ A, work (f i) ≤ B) : work (productFinset A f) ≤ 1 + A.card * (B + 1) := by
  simpa only [productFinset, Finset.length_sort] using
    work_productList_le (A.sort (· ≤ ·)) f B (fun i hi => h i ((A.mem_sort (· ≤ ·)).mp hi))

end ArithmeticExpression
end ProphetSecretary.Analysis
