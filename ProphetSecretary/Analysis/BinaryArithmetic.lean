import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Counted binary addition and multiplication

Words are lists of bits with the least significant bit first. Addition is a
ripple-carry scan. Multiplication adds the shifted partial product at each
nonzero digit. The counters include the fixed number of Boolean operations
and list steps in each digit update.
-/

namespace ProphetSecretary.Analysis

def bitDigit (b : Bool) : ℕ := if b then 1 else 0

def binaryWordValue : List Bool → ℕ
  | [] => 0
  | b :: l => bitDigit b + 2 * binaryWordValue l

lemma binaryWordValue_head_tail (x : List Bool) :
    binaryWordValue x = bitDigit (x.headD false) + 2 * binaryWordValue x.tail := by
  cases x <;> rfl

lemma binaryWordValue_lt_pow (x : List Bool) : binaryWordValue x < 2^x.length := by
  induction x with
  | nil => decide
  | cons b x ih => cases b <;> simp [binaryWordValue, bitDigit, pow_succ] <;> omega

def fullAdder (a b c : Bool) : Bool × Bool :=
  ((a ^^ b) ^^ c, (a && b) || (c && (a || b)))

lemma fullAdder_correct (a b c : Bool) :
    bitDigit (fullAdder a b c).1 + 2*bitDigit (fullAdder a b c).2 =
      bitDigit a + bitDigit b + bitDigit c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Add two padded words of the declared width, emitting the final carry. -/
def countedBinaryAdd : ℕ → List Bool → List Bool → Bool → List Bool × ℕ
  | 0, _, _, c => (if c then [true] else [], 1)
  | d+1, x, y, c =>
    let h := fullAdder (x.headD false) (y.headD false) c
    let t := countedBinaryAdd d x.tail y.tail h.2
    (h.1 :: t.1,t.2+12)

lemma countedBinaryAdd_value (d : ℕ) (x y : List Bool) (c : Bool)
    (hx : x.length ≤ d) (hy : y.length ≤ d) :
    binaryWordValue (countedBinaryAdd d x y c).1 =
      binaryWordValue x + binaryWordValue y + bitDigit c := by
  induction d generalizing x y c with
  | zero =>
    have he : x = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hx)
    have hf : y = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hy)
    subst x
    subst y
    cases c <;> decide
  | succ d ih =>
    let h := fullAdder (x.headD false) (y.headD false) c
    have hx' : x.tail.length ≤ d := by cases x <;> simp_all
    have hy' : y.tail.length ≤ d := by cases y <;> simp_all
    have hc := fullAdder_correct (x.headD false) (y.headD false) c
    change bitDigit h.1 + 2 * binaryWordValue (countedBinaryAdd d x.tail y.tail h.2).1 = _
    rw [ih _ _ _ hx' hy']
    have hX := binaryWordValue_head_tail x
    have hY := binaryWordValue_head_tail y
    change bitDigit h.1 + 2*bitDigit h.2 = _ at hc
    omega

lemma countedBinaryAdd_length (d : ℕ) (x y : List Bool) (c : Bool) :
    (countedBinaryAdd d x y c).1.length ≤ d+1 := by
  induction d generalizing x y c with
  | zero => cases c <;> simp [countedBinaryAdd]
  | succ d ih =>
    simp only [countedBinaryAdd, List.length_cons]
    exact Nat.add_le_add_right (ih _ _ _) 1

lemma countedBinaryAdd_work (d : ℕ) (x y : List Bool) (c : Bool) :
    (countedBinaryAdd d x y c).2 = 12*d+1 := by
  induction d generalizing x y c with
  | zero => rfl
  | succ d ih => simp only [countedBinaryAdd, ih]; omega

/-- Schoolbook multiplication, with explicit shifts and padded additions. -/
def countedBinaryMultiply : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([],1)
  | b :: x, y =>
    let p := countedBinaryMultiply x y
    let s := false :: p.1
    if b then
      let d := max s.length y.length
      let a := countedBinaryAdd d s y false
      (a.1,p.2+a.2+2*(s.length+y.length)+8)
    else (s,p.2+4)

lemma countedBinaryMultiply_value (x y : List Bool) :
    binaryWordValue (countedBinaryMultiply x y).1 = binaryWordValue x * binaryWordValue y := by
  induction x with
  | nil => simp [countedBinaryMultiply,binaryWordValue]
  | cons b x ih =>
    let p := countedBinaryMultiply x y
    let s := false :: p.1
    cases b
    · change binaryWordValue s = (0+2*binaryWordValue x)*binaryWordValue y
      simp only [s,binaryWordValue,bitDigit,Bool.false_eq_true,if_false,zero_add,p,ih,mul_assoc]
    · change binaryWordValue (countedBinaryAdd (max s.length y.length) s y false).1 =
        (1+2*binaryWordValue x)*binaryWordValue y
      rw [countedBinaryAdd_value _ _ _ _ (le_max_left _ _) (le_max_right _ _)]
      simp only [s,binaryWordValue,bitDigit,Bool.false_eq_true,if_false,zero_add,p,ih,add_zero,add_mul,one_mul]
      ac_rfl

lemma countedBinaryMultiply_length (x y : List Bool) :
    (countedBinaryMultiply x y).1.length ≤ 2*x.length+y.length := by
  induction x with
  | nil => simp [countedBinaryMultiply]
  | cons b x ih =>
    let p := countedBinaryMultiply x y
    let s := false :: p.1
    have hs : s.length ≤ 2*x.length+y.length+1 := Nat.add_le_add_right ih 1
    cases b
    · change s.length ≤ 2*(x.length+1)+y.length
      omega
    · change (countedBinaryAdd (max s.length y.length) s y false).1.length ≤ 2*(x.length+1)+y.length
      have hd : max s.length y.length ≤ 2*x.length+y.length+1 := max_le hs (by omega)
      exact (countedBinaryAdd_length _ _ _ _).trans (by omega)

theorem countedBinaryMultiply_work (x y : List Bool) :
    (countedBinaryMultiply x y).2 ≤ 32*(x.length+1)*(2*x.length+y.length+2) := by
  induction x with
  | nil =>
    simp only [countedBinaryMultiply,List.length_nil,zero_add,mul_zero,mul_one]
    omega
  | cons b x ih =>
    let p := countedBinaryMultiply x y
    let s := false :: p.1
    have hs : s.length ≤ 2*x.length+y.length+1 := Nat.add_le_add_right (countedBinaryMultiply_length x y) 1
    have hd : max s.length y.length ≤ 2*x.length+y.length+1 := max_le hs (by omega)
    have hp : p.2 ≤ 32*(x.length+1)*(2*x.length+y.length+2) := ih
    have hi : 12*max s.length y.length+1+2*(s.length+y.length)+8 ≤ 32*(2*x.length+y.length+2) := by omega
    cases b
    · change p.2+4 ≤ 32*(x.length+1+1)*(2*(x.length+1)+y.length+2)
      nlinarith
    · change p.2+(countedBinaryAdd (max s.length y.length) s y false).2+2*(s.length+y.length)+8 ≤
        32*(x.length+1+1)*(2*(x.length+1)+y.length+2)
      rw [countedBinaryAdd_work]
      nlinarith

end ProphetSecretary.Analysis
