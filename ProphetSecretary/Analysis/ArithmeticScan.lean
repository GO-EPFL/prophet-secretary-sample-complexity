import ProphetSecretary.Analysis.ArithmeticExpression

/-!
# A counted finite minimum scan

At each list entry the scan evaluates one arithmetic threshold, makes one
scalar comparison, and, on a crossing, compares two identities. A list step
costs one further unit. The fallback read costs one unit. The counter records
the actual branch taken.
-/

namespace ProphetSecretary.Analysis
open ArithmeticExpression

variable {ι α K : Type*}

def arithmeticMinimumScan [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (e : α → ArithmeticExpression ι)
    (x : ι → K) (u : K) (fallback : α) : α × ℕ :=
  match l with
  | [] => (fallback, 1)
  | i :: l =>
      let tail := arithmeticMinimumScan l e x u fallback
      if u < eval x (e i) then (min i tail.1, tail.2 + work (e i) + 3)
      else (tail.1, tail.2 + work (e i) + 2)

lemma arithmeticMinimumScan_le_fallback [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (e : α → ArithmeticExpression ι)
    (x : ι → K) (u : K) (fallback : α) : (arithmeticMinimumScan l e x u fallback).1 ≤ fallback := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
    unfold arithmeticMinimumScan
    split_ifs
    · exact (min_le_right _ _).trans ih
    · exact ih

lemma arithmeticMinimumScan_le_candidate [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (e : α → ArithmeticExpression ι)
    (x : ι → K) (u : K) (fallback : α) {j : α} (hj : j ∈ l) (hCross : u < eval x (e j)) :
    (arithmeticMinimumScan l e x u fallback).1 ≤ j := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    unfold arithmeticMinimumScan
    split_ifs with hi
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih hj)
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact False.elim (hi hCross)
      · exact ih hj

lemma le_arithmeticMinimumScan [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (e : α → ArithmeticExpression ι)
    (x : ι → K) (u : K) (fallback k : α) (hk : k ≤ fallback)
    (h : ∀ i ∈ l, u < eval x (e i) → k ≤ i) : k ≤ (arithmeticMinimumScan l e x u fallback).1 := by
  induction l with
  | nil => exact hk
  | cons i l ih =>
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    unfold arithmeticMinimumScan
    split_ifs with hi
    · exact le_min (h i (List.mem_cons_self) hi) ht
    · exact ht

/-- The scan terminates with a deterministic polynomial bound on every input. -/
lemma arithmeticMinimumScan_work_le [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (e : α → ArithmeticExpression ι)
    (x : ι → K) (u : K) (fallback : α) (B : ℕ) (h : ∀ i ∈ l, work (e i) ≤ B) :
    (arithmeticMinimumScan l e x u fallback).2 ≤ 1 + l.length * (B + 3) := by
  induction l with
  | nil => simp [arithmeticMinimumScan]
  | cons i l ih =>
    have hi := h i (List.mem_cons_self)
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have he : 1 + (l.length + 1) * (B + 3) = 1 + l.length * (B + 3) + B + 3 := by ring
    simp only [List.length_cons, he]
    unfold arithmeticMinimumScan
    split_ifs <;> dsimp only <;> omega

/-- A comparison filter counts its predicate call and list step, and also
counts construction of an output cell when the comparison succeeds. -/
def countedPredicateFilter (p : α → Prop) [DecidablePred p] : List α → List α × ℕ
  | [] => ([], 1)
  | i :: l =>
      let tail := countedPredicateFilter p l
      if p i then (i :: tail.1, tail.2 + 3) else (tail.1, tail.2 + 2)

lemma countedPredicateFilter_value (p : α → Prop) [DecidablePred p] (l : List α) :
    (countedPredicateFilter p l).1 = l.filter (fun i => decide (p i)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : p i <;> simp [countedPredicateFilter, hi, ih]

lemma countedPredicateFilter_work (p : α → Prop) [DecidablePred p] (l : List α) :
    (countedPredicateFilter p l).2 ≤ 1 + 3 * l.length := by
  induction l with
  | nil => simp [countedPredicateFilter]
  | cons i l ih =>
    unfold countedPredicateFilter
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

def countedSumExpression {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) : ArithmeticExpression ι × ℕ :=
  match l with
  | [] => (.integer 0, 1)
  | i :: l =>
      let head := g i
      let tail := countedSumExpression l g
      (.add head.1 tail.1, head.2 + tail.2 + 2)

def countedProductExpression {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) : ArithmeticExpression ι × ℕ :=
  match l with
  | [] => (.integer 1, 1)
  | i :: l =>
      let head := g i
      let tail := countedProductExpression l g
      (.mul head.1 tail.1, head.2 + tail.2 + 2)

lemma countedSumExpression_value {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) :
    (countedSumExpression l g).1 = sumList l (fun i => (g i).1) := by
  induction l <;> simp_all [countedSumExpression, sumList]

lemma countedProductExpression_value {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) :
    (countedProductExpression l g).1 = productList l (fun i => (g i).1) := by
  induction l <;> simp_all [countedProductExpression, productList]

lemma countedSumExpression_work {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) (G : ℕ) (h : ∀ i ∈ l, (g i).2 ≤ G) :
    (countedSumExpression l g).2 ≤ 1 + l.length * (G + 2) := by
  induction l with
  | nil => simp [countedSumExpression]
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    dsimp only [countedSumExpression]
    simp only [List.length_cons]
    have he : 1 + (l.length + 1) * (G + 2) = G + (1 + l.length * (G + 2)) + 2 := by ring
    rw [he]
    omega

lemma countedProductExpression_work {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) (G : ℕ) (h : ∀ i ∈ l, (g i).2 ≤ G) :
    (countedProductExpression l g).2 ≤ 1 + l.length * (G + 2) := by
  induction l with
  | nil => simp [countedProductExpression]
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    dsimp only [countedProductExpression]
    simp only [List.length_cons]
    have he : 1 + (l.length + 1) * (G + 2) = G + (1 + l.length * (G + 2)) + 2 := by ring
    rw [he]
    omega

/-- Threshold construction is charged before its arithmetic evaluation. -/
def arithmeticGeneratedMinimumScan [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (g : α → ArithmeticExpression ι × ℕ)
    (x : ι → K) (u : K) (fallback : α) : α × ℕ :=
  match l with
  | [] => (fallback, 1)
  | i :: l =>
      let tail := arithmeticGeneratedMinimumScan l g x u fallback
      let head := g i
      if u < eval x head.1 then (min i tail.1, tail.2 + head.2 + work head.1 + 3)
      else (tail.1, tail.2 + head.2 + work head.1 + 2)

lemma arithmeticGeneratedMinimumScan_value [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (g : α → ArithmeticExpression ι × ℕ)
    (x : ι → K) (u : K) (fallback : α) :
    (arithmeticGeneratedMinimumScan l g x u fallback).1 =
      (arithmeticMinimumScan l (fun i => (g i).1) x u fallback).1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases h : u < eval x (g i).1 <;>
      simp [arithmeticGeneratedMinimumScan, arithmeticMinimumScan, h, ih]

lemma arithmeticGeneratedMinimumScan_work [LinearOrder α] [Field K] [LinearOrder K] (l : List α) (g : α → ArithmeticExpression ι × ℕ)
    (x : ι → K) (u : K) (fallback : α) (G B : ℕ)
    (hG : ∀ i ∈ l, (g i).2 ≤ G) (hB : ∀ i ∈ l, work (g i).1 ≤ B) :
    (arithmeticGeneratedMinimumScan l g x u fallback).2 ≤ 1 + l.length * (G + B + 3) := by
  induction l with
  | nil => simp [arithmeticGeneratedMinimumScan]
  | cons i l ih =>
    have hg := hG i List.mem_cons_self
    have hb := hB i List.mem_cons_self
    have ht := ih (fun j hj => hG j (List.mem_cons_of_mem _ hj))
      (fun j hj => hB j (List.mem_cons_of_mem _ hj))
    have he : 1 + (l.length + 1) * (G + B + 3) =
        (1 + l.length * (G + B + 3)) + G + B + 3 := by ring
    simp only [List.length_cons, he]
    unfold arithmeticGeneratedMinimumScan
    dsimp only
    split_ifs <;> dsimp only <;> omega

def countedMaximumExpression {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) : ArithmeticExpression ι × ℕ :=
  match l with
  | [] => (.integer 0, 1)
  | i :: l =>
      let head := g i
      let tail := countedMaximumExpression l g
      (.maximum head.1 tail.1, head.2 + tail.2 + 2)

lemma countedMaximumExpression_value {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) :
    (countedMaximumExpression l g).1 = maximumList l (fun i => (g i).1) := by
  induction l <;> simp_all [countedMaximumExpression, maximumList]

lemma countedMaximumExpression_work {β : Type*} (l : List β)
    (g : β → ArithmeticExpression ι × ℕ) (G : ℕ) (h : ∀ i ∈ l, (g i).2 ≤ G) :
    (countedMaximumExpression l g).2 ≤ 1 + l.length * (G + 2) := by
  induction l with
  | nil => simp [countedMaximumExpression]
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    dsimp only [countedMaximumExpression]
    simp only [List.length_cons]
    have he : 1 + (l.length + 1) * (G + 2) = G + (1 + l.length * (G + 2)) + 2 := by ring
    rw [he]
    omega

def countedListLength {β : Type*} : List β → ℕ × ℕ
  | [] => (0, 1)
  | _ :: l => let q := countedListLength l; (q.1 + 1, q.2 + 2)

@[simp] lemma countedListLength_value {β : Type*} (l : List β) : (countedListLength l).1 = l.length := by
  induction l <;> simp_all [countedListLength]

@[simp] lemma countedListLength_work {β : Type*} (l : List β) : (countedListLength l).2 = 1 + 2 * l.length := by
  induction l with
  | nil => simp [countedListLength]
  | cons i l ih =>
    simp only [countedListLength, List.length_cons, ih]
    omega

def countedListContains {β : Type*} [DecidableEq β] (a : β) : List β → Bool × ℕ
  | [] => (false, 1)
  | i :: l => if a = i then (true, 2) else
      let q := countedListContains a l
      (q.1, q.2 + 2)

@[simp] lemma countedListContains_value {β : Type*} [DecidableEq β] (a : β) (l : List β) :
    (countedListContains a l).1 = decide (a ∈ l) := by
  induction l with
  | nil => simp [countedListContains]
  | cons i l ih =>
    by_cases hi : a = i <;> simp [countedListContains, hi, ih]

lemma countedListContains_work {β : Type*} [DecidableEq β] (a : β) (l : List β) :
    (countedListContains a l).2 ≤ 1 + 2 * l.length := by
  induction l with
  | nil => simp [countedListContains]
  | cons i l ih =>
    unfold countedListContains
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

def countedMaximumScan [LinearOrder α] (fallback : α) : List α → α × ℕ
  | [] => (fallback, 1)
  | i :: l => let q := countedMaximumScan fallback l; (max i q.1, q.2 + 2)

lemma countedMaximumScan_work [LinearOrder α] (fallback : α) (l : List α) :
    (countedMaximumScan fallback l).2 = 1 + 2 * l.length := by
  induction l with
  | nil => simp [countedMaximumScan]
  | cons i l ih =>
    simp only [countedMaximumScan, List.length_cons, ih]
    omega

lemma le_countedMaximumScan_fallback [LinearOrder α] (fallback : α) (l : List α) :
    fallback ≤ (countedMaximumScan fallback l).1 := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact ih.trans (le_max_right _ _)

lemma le_countedMaximumScan_of_mem [LinearOrder α] (fallback : α) (l : List α)
    {a : α} (ha : a ∈ l) : a ≤ (countedMaximumScan fallback l).1 := by
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

lemma countedMaximumScan_le [LinearOrder α] (fallback : α) (l : List α) (k : α)
    (hf : fallback ≤ k) (h : ∀ i ∈ l, i ≤ k) : (countedMaximumScan fallback l).1 ≤ k := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    exact max_le (h i List.mem_cons_self) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma arithmeticMinimumScan_mem [LinearOrder α] [Field K] [LinearOrder K]
    (l : List α) (e : α → ArithmeticExpression ι) (x : ι → K) (u : K) (fallback : α) :
    (arithmeticMinimumScan l e x u fallback).1 ∈ fallback :: l := by
  induction l with
  | nil => exact List.mem_cons_self
  | cons i l ih =>
    have ht : (arithmeticMinimumScan l e x u fallback).1 ∈ fallback :: i :: l := by
      rcases List.mem_cons.mp ih with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
    unfold arithmeticMinimumScan
    split_ifs <;> dsimp only
    · by_cases hle : i ≤ (arithmeticMinimumScan l e x u fallback).1
      · rw [min_eq_left hle]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [min_eq_right (lt_of_not_ge hle).le]
        exact ht
    · exact ht

lemma countedMaximumScan_mem [LinearOrder α] (fallback : α) (l : List α) :
    (countedMaximumScan fallback l).1 ∈ fallback :: l := by
  induction l with
  | nil => exact List.mem_cons_self
  | cons i l ih =>
    have ht : (countedMaximumScan fallback l).1 ∈ fallback :: i :: l := by
      rcases List.mem_cons.mp ih with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
    dsimp only [countedMaximumScan]
    by_cases hle : i ≤ (countedMaximumScan fallback l).1
    · rw [max_eq_right hle]
      exact ht
    · rw [max_eq_left (lt_of_not_ge hle).le]
      exact List.mem_cons_of_mem _ List.mem_cons_self

end ProphetSecretary.Analysis
