import ProphetSecretary.Probability.CountedMedian
import ProphetSecretary.Analysis.BinaryRationalWork

/-!
# The counted median with binary comparisons

Each copy is evaluated once. Insertion sorting then compares their stored
binary words, preserving the exact median of the rational outputs.
-/

namespace ProphetSecretary.Probability
open ProphetSecretary.Analysis

def countedBinaryInsert (a : BinaryRational) : List BinaryRational → List BinaryRational × ℕ
  | [] => ([a],1)
  | b::l =>
    let c := b.storage.countedLE a.storage
    if c.1 then (a::b::l,c.2+4) else
      let q := countedBinaryInsert a l
      (b::q.1,c.2+q.2+4)

lemma countedBinaryInsert_value (a : BinaryRational) (l : List BinaryRational) :
    (countedBinaryInsert a l).1=List.orderedInsert (fun x y => y≤x) a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have h : (b.storage.countedLE a.storage).1=true ↔ b≤a :=
      BinaryFraction.countedLE_correct _ _ (BinaryRational.storage_denominator_pos b) (BinaryRational.storage_denominator_pos a)
    by_cases he : b≤a
    · simp only [countedBinaryInsert,if_pos (h.mpr he),List.orderedInsert,if_pos he]
    · simp only [countedBinaryInsert,if_neg (mt h.mp he),List.orderedInsert,if_neg he,ih]

def countedBinaryInsertionSort : List BinaryRational → List BinaryRational × ℕ
  | [] => ([],1)
  | a::l =>
    let q := countedBinaryInsertionSort l
    let s := countedBinaryInsert a q.1
    (s.1,q.2+s.2+2)

lemma countedBinaryInsertionSort_value (l : List BinaryRational) :
    (countedBinaryInsertionSort l).1=List.insertionSort (fun a b => b≤a) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [countedBinaryInsertionSort,countedBinaryInsert_value,ih,List.insertionSort_cons]

lemma countedBinaryInsert_work (a : BinaryRational) (l : List BinaryRational) (B : ℕ)
    (ha : RationalHeight a.value B) (hL : ∀ x ∈ l, RationalHeight x.value B) :
    (countedBinaryInsert a l).2≤(l.length+1)*(3400*(B+2)^3+5) := by
  let C := 3400*(B+2)^3+5
  change (countedBinaryInsert a l).2≤(l.length+1)*C
  induction l with
  | nil => change 1≤_; dsimp [C]; omega
  | cons b l ih =>
    let c := b.storage.countedLE a.storage
    have hB := hL b List.mem_cons_self
    have hc : c.2≤3400*(B+2)^3 := BinaryFraction.countedLE_work _ _ (B+1)
      (BinaryRational.storage_width b B hB) (BinaryRational.storage_width a B ha)
      (BinaryRational.storage_denominator_pos b) (BinaryRational.storage_denominator_pos a)
    have h := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    have hC : c.2+4≤C := by dsimp [C]; omega
    unfold countedBinaryInsert
    dsimp only
    split_ifs
    · change c.2+4≤(l.length+1+1)*C
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · change c.2+(countedBinaryInsert a l).2+4≤(l.length+1+1)*C
      rw [Nat.add_mul,Nat.one_mul]
      omega

theorem countedBinaryInsertionSort_work (l : List BinaryRational) (B : ℕ)
    (hL : ∀ x ∈ l, RationalHeight x.value B) :
    (countedBinaryInsertionSort l).2≤2*(l.length+1)^2*(3400*(B+2)^3+5) := by
  let C := 3400*(B+2)^3+5
  change (countedBinaryInsertionSort l).2≤2*(l.length+1)^2*C
  induction l with
  | nil => change 1≤2*C; dsimp [C]; omega
  | cons a l ih =>
    let q := countedBinaryInsertionSort l
    have hL' (x : BinaryRational) (hx : x∈l) : RationalHeight x.value B := hL x (List.mem_cons_of_mem _ hx)
    have hq : q.2≤2*(l.length+1)^2*C := ih hL'
    have hqL (x : BinaryRational) (hx : x∈q.1) : RationalHeight x.value B := by
      rw [countedBinaryInsertionSort_value,List.mem_insertionSort] at hx
      exact hL' x hx
    have hlen : q.1.length=l.length := by rw [countedBinaryInsertionSort_value,List.length_insertionSort]
    have hA := countedBinaryInsert_work a q.1 B (hL a List.mem_cons_self) hqL
    rw [hlen] at hA
    have hI : (countedBinaryInsert a q.1).2≤(l.length+1)*C := hA
    change q.2+(countedBinaryInsert a q.1).2+2≤2*(l.length+1+1)^2*C
    have hC : 2≤C := by dsimp [C]; omega
    calc
      _ ≤ (2*(l.length+1)^2+(l.length+1)+1)*C := by rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith)

def countedBinaryMedianCopies {Seed : Type*} (a : ℕ) (call : Seed → BinaryRational × ℕ)
    (s : Fin (2*a+1) → Seed) : MedianCopiesResult BinaryRational :=
  let raw := List.ofFn (fun i => call (s i))
  let sorted := countedBinaryInsertionSort (raw.map Prod.fst)
  have h : a<sorted.1.length := by
    rw [show sorted.1=(List.insertionSort (fun x y => y≤x) (raw.map Prod.fst)) from countedBinaryInsertionSort_value _,
      List.length_insertionSort,List.length_map]
    simp [raw]
    omega
  { value := sorted.1.get ⟨a,h⟩,copies := 2*a+1,
    work := sorted.2+(raw.map Prod.snd).sum+6*(2*a+2)+2 }

lemma countedBinaryMedianCopies_value {Seed : Type*} (a : ℕ) (call : Seed → BinaryRational × ℕ)
    (s : Fin (2*a+1) → Seed) :
    (countedBinaryMedianCopies a call s).value=sortedMedian a (fun i => (call (s i)).1) := by
  have h : (countedBinaryInsertionSort ((List.ofFn fun i => call (s i)).map Prod.fst)).1 =
      List.insertionSort (fun x y => y≤x) (List.ofFn (fun i => (call (s i)).1)) := by
    rw [countedBinaryInsertionSort_value,List.map_ofFn]
    rfl
  have he := congrArg (fun l : List BinaryRational => l[a]?) h
  have hl : a<(countedBinaryInsertionSort ((List.ofFn fun i => call (s i)).map Prod.fst)).1.length := by
    rw [h,List.length_insertionSort,List.length_ofFn]
    omega
  have hr : a<(List.insertionSort (fun x y => y≤x) (List.ofFn (fun i => (call (s i)).1))).length := by
    rw [List.length_insertionSort,List.length_ofFn]
    omega
  rw [List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr] at he
  exact Option.some.inj he

theorem countedBinaryMedianCopies_work {Seed : Type*} (a : ℕ) (call : Seed → BinaryRational × ℕ)
    (s : Fin (2*a+1) → Seed) (B W : ℕ) (h : ∀ i, RationalHeight (call (s i)).1.value B ∧ (call (s i)).2≤W) :
    (countedBinaryMedianCopies a call s).work≤
      2*(2*a+2)^2*(3400*(B+2)^3+5)+(2*a+1)*W+6*(2*a+2)+2 := by
  let raw := List.ofFn (fun i => call (s i))
  have hR (x : BinaryRational) (hx : x∈raw.map Prod.fst) : RationalHeight x.value B := by
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
    exact (h i).1
  have hS := countedBinaryInsertionSort_work (raw.map Prod.fst) B hR
  have hLen : (raw.map Prod.fst).length=2*a+1 := by simp [raw]
  rw [hLen] at hS
  have hC : (raw.map Prod.snd).sum≤(2*a+1)*W := by
    simp only [raw,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    calc
      _ ≤ ∑ _ : Fin (2*a+1), W := Finset.sum_le_sum (fun i _ => (h i).2)
      _ = _ := by simp
  change (countedBinaryInsertionSort (raw.map Prod.fst)).2+(raw.map Prod.snd).sum+6*(2*a+2)+2≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hS hC) _) _

end ProphetSecretary.Probability
