import ProphetSecretary.Statistics.PlannerNumericBits
import ProphetSecretary.Statistics.PlannerChoiceWork
import ProphetSecretary.Analysis.BinaryRationalWork

/-!
# The categorical scan on binary words

For every inspected label the scan generates its actual prefix expression,
evaluates it on binary fractions, and makes one counted binary comparison.
The result and its work are returned by the same scan.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

def countedBinaryMinimumScan {α ι : Type*} [LinearOrder α]
    (g : α → ArithmeticExpression ι × ℕ) (x : ι → BinaryRational) (u : BinaryRational)
    (fallback : α) : List α → α × ℕ
  | [] => (fallback,1)
  | i::l =>
    let e := g i
    let v := countedBinaryEval (fun j => (x j).storage) e.1
    let c := v.1.countedLE u.storage
    let q := countedBinaryMinimumScan g x u fallback l
    (if c.1 then q.1 else min i q.1,q.2+e.2+v.2+c.2+5)

theorem countedBinaryMinimumScan_value {α ι : Type*} [LinearOrder α]
    (g : α → ArithmeticExpression ι × ℕ) (x : ι → BinaryRational) (u : BinaryRational)
    (fallback : α) (l : List α) :
    (countedBinaryMinimumScan g x u fallback l).1 =
      (arithmeticGeneratedMinimumScan l g (fun j => (x j).value) u.value fallback).1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    let v := countedBinaryEval (fun j => (x j).storage) (g i).1
    let q := countedBinaryMinimumScan g x u fallback l
    have hV := countedBinaryEval_semantics (fun j => (x j).storage)
      (fun j => BinaryRational.storage_denominator_pos (x j)) (g i).1
    have hV' : v.1.value=eval (fun j => (x j).value) (g i).1 := hV.1
    have h : (v.1.countedLE u.storage).1=true ↔
        eval (fun j => (x j).value) (g i).1≤u.value := by
      rw [← hV']
      exact BinaryFraction.countedLE_correct v.1 u.storage hV.2 (BinaryRational.storage_denominator_pos u)
    by_cases he : u.value < eval (fun j => (x j).value) (g i).1
    · have hn : ¬(v.1.countedLE u.storage).1=true := mt h.mp (not_le.mpr he)
      dsimp only [v] at hn
      simp only [countedBinaryMinimumScan,if_neg hn,arithmeticGeneratedMinimumScan,if_pos he,ih]
    · have hp := h.mpr (le_of_not_gt he)
      dsimp only [v] at hp
      simp only [countedBinaryMinimumScan,if_pos hp,arithmeticGeneratedMinimumScan,if_neg he,ih]

def binaryPrefixScanUnit (B W G : ℕ) : ℕ :=
  G+W*(3500*((B+1)*W+2)^3)+3400*((B+1)*W+2)^3+5

theorem countedBinaryMinimumScan_work {α ι : Type*} [LinearOrder α]
    (g : α → ArithmeticExpression ι × ℕ) (x : ι → BinaryRational) (u : BinaryRational)
    (fallback : α) (l : List α) (B W G : ℕ) (hW : 1≤W)
    (hX : ∀ i, RationalHeight (x i).value B) (hU : RationalHeight u.value B)
    (hG : ∀ i ∈ l, LiteralsBounded B (g i).1 ∧ (g i).1.work≤W ∧ (g i).2≤G) :
    (countedBinaryMinimumScan g x u fallback l).2 ≤ 1+l.length*binaryPrefixScanUnit B W G := by
  let C := binaryPrefixScanUnit B W G
  have hx (i : ι) : 0<binaryWordValue (x i).storage.denominator ∧ (x i).storage.width≤B+1 ∧
      RationalHeight (x i).storage.value B :=
    ⟨BinaryRational.storage_denominator_pos _,BinaryRational.storage_width _ B (hX i),hX i⟩
  change (countedBinaryMinimumScan g x u fallback l).2 ≤ 1+l.length*C
  induction l with
  | nil => simp [countedBinaryMinimumScan]
  | cons i l ih =>
    let v := countedBinaryEval (fun j => (x j).storage) (g i).1
    let q := countedBinaryMinimumScan g x u fallback l
    let D := (B+1)*W+1
    have he := hG i List.mem_cons_self
    have hv := countedBinaryEval_correct (fun j => (x j).storage) B hx (g i).1 he.1
    have hvW : v.1.width≤D := hv.2.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ he.2.1) 1)
    have huW : u.storage.width≤D := (BinaryRational.storage_width u B hU).trans
      ((Nat.le_mul_of_pos_right (B+1) hW).trans (Nat.le_succ _))
    have hComp : (v.1.countedLE u.storage).2≤3400*(D+1)^3 :=
      BinaryFraction.countedLE_work v.1 u.storage D hvW huW hv.2.1 (BinaryRational.storage_denominator_pos u)
    have hEval : v.2≤W*(3500*((B+1)*W+2)^3) :=
      binaryExpression_work_le (fun j => (x j).storage) B W hx (g i).1 he.1 he.2.1
    have hTail : q.2≤1+l.length*C := ih (fun j hj => hG j (List.mem_cons_of_mem _ hj))
    have hStep : (g i).2+v.2+(v.1.countedLE u.storage).2+5≤C := by
      dsimp [C,binaryPrefixScanUnit]
      change (v.1.countedLE u.storage).2≤3400*((B+1)*W+2)^3 at hComp
      omega
    change q.2+(g i).2+v.2+(v.1.countedLE u.storage).2+5≤1+(l.length+1)*C
    rw [Nat.add_mul,Nat.one_mul]
    omega

end ProphetSecretary.Statistics
