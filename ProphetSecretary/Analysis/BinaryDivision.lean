import ProphetSecretary.Analysis.BinaryArithmetic
import Mathlib.Tactic.Ring

/-!
# Counted binary comparison and long division

The subtraction scan exposes the final borrow. Long division uses it at each
digit to compare with the divisor and, when necessary, subtract once. At
each prefix the stored remainder is smaller than the positive divisor.
-/

namespace ProphetSecretary.Analysis

lemma bitDigit_le_one (b : Bool) : bitDigit b ≤ 1 := by cases b <;> decide

def fullSubtractor (a b c : Bool) : Bool × Bool :=
  ((a ^^ b) ^^ c, (!a && b) || (c && !(a ^^ b)))

lemma fullSubtractor_correct (a b c : Bool) :
    bitDigit a+2*bitDigit (fullSubtractor a b c).2 =
      bitDigit b+bitDigit c+bitDigit (fullSubtractor a b c).1 := by
  cases a <;> cases b <;> cases c <;> decide

def countedBinarySubtract : ℕ → List Bool → List Bool → Bool → (List Bool × Bool) × ℕ
  | 0, _, _, c => (([],c),1)
  | d+1, x, y, c =>
    let h := fullSubtractor (x.headD false) (y.headD false) c
    let t := countedBinarySubtract d x.tail y.tail h.2
    ((h.1 :: t.1.1,t.1.2),t.2+14)

lemma countedBinarySubtract_length (d : ℕ) (x y : List Bool) (c : Bool) :
    (countedBinarySubtract d x y c).1.1.length = d := by
  induction d generalizing x y c with
  | zero => rfl
  | succ d ih => simp only [countedBinarySubtract, List.length_cons, ih]

lemma countedBinarySubtract_work (d : ℕ) (x y : List Bool) (c : Bool) :
    (countedBinarySubtract d x y c).2 = 14*d+1 := by
  induction d generalizing x y c with
  | zero => rfl
  | succ d ih => simp only [countedBinarySubtract, ih]; omega

lemma countedBinarySubtract_value (d : ℕ) (x y : List Bool) (c : Bool)
    (hx : x.length ≤ d) (hy : y.length ≤ d) :
    let t := countedBinarySubtract d x y c
    binaryWordValue x+2^d*bitDigit t.1.2 = binaryWordValue y+bitDigit c+binaryWordValue t.1.1 := by
  induction d generalizing x y c with
  | zero =>
    have he : x = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hx)
    have hf : y = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hy)
    subst x
    subst y
    simp [countedBinarySubtract,binaryWordValue]
  | succ d ih =>
    let h := fullSubtractor (x.headD false) (y.headD false) c
    let t := countedBinarySubtract d x.tail y.tail h.2
    have hx' : x.tail.length ≤ d := by cases x <;> simp_all
    have hy' : y.tail.length ≤ d := by cases y <;> simp_all
    have ht : binaryWordValue x.tail+2^d*bitDigit t.1.2 =
        binaryWordValue y.tail+bitDigit h.2+binaryWordValue t.1.1 := ih _ _ _ hx' hy'
    have hb := fullSubtractor_correct (x.headD false) (y.headD false) c
    change bitDigit (x.headD false)+2*bitDigit h.2 =
      bitDigit (y.headD false)+bitDigit c+bitDigit h.1 at hb
    have hX := binaryWordValue_head_tail x
    have hY := binaryWordValue_head_tail y
    change binaryWordValue x+2^(d+1)*bitDigit t.1.2 =
      binaryWordValue y+bitDigit c+(bitDigit h.1+2*binaryWordValue t.1.1)
    rw [show 2^(d+1)*bitDigit t.1.2 = 2*(2^d*bitDigit t.1.2) by rw [pow_succ]; ring]
    omega

lemma countedBinarySubtract_borrow_iff (d : ℕ) (x y : List Bool) (c : Bool)
    (hx : x.length ≤ d) (hy : y.length ≤ d) :
    (countedBinarySubtract d x y c).1.2 = true ↔ binaryWordValue x < binaryWordValue y+bitDigit c := by
  let q := countedBinarySubtract d x y c
  have hV := countedBinarySubtract_value d x y c hx hy
  have hL := binaryWordValue_lt_pow q.1.1
  rw [show q.1.1.length=d from countedBinarySubtract_length d x y c] at hL
  change binaryWordValue x+2^d*bitDigit q.1.2 =
    binaryWordValue y+bitDigit c+binaryWordValue q.1.1 at hV
  change q.1.2 = true ↔ _
  cases hq : q.1.2 <;> simp [hq, bitDigit] at hV ⊢ <;> omega

lemma binaryWordValue_take_of_lt (x : List Bool) (d : ℕ) (hx : binaryWordValue x < 2^d) :
    binaryWordValue (x.take d) = binaryWordValue x := by
  induction d generalizing x with
  | zero => simp only [List.take_zero, binaryWordValue, pow_zero] at hx ⊢; omega
  | succ d ih =>
    cases x with
    | nil => rfl
    | cons b x =>
      have ht : binaryWordValue x < 2^d := by simp only [binaryWordValue,pow_succ] at hx; omega
      simp only [List.take_succ_cons,binaryWordValue,ih x ht]

/-- Quotient and remainder from the high prefix followed by one low bit. -/
def countedBinaryDivide (d : ℕ) (y : List Bool) : List Bool → (List Bool × List Bool) × ℕ
  | [] => (([],[]),1)
  | b :: x =>
    let p := countedBinaryDivide d y x
    let s := b :: p.1.2
    let c := countedBinarySubtract (d+1) s y false
    let q := !c.1.2
    let rem := (if c.1.2 then s else c.1.1).take d
    ((q :: p.1.1,rem),p.2+c.2+2*d+8)

lemma countedBinaryDivide_lengths (d : ℕ) (x y : List Bool) :
    (countedBinaryDivide d y x).1.1.length = x.length ∧
      (countedBinaryDivide d y x).1.2.length ≤ d := by
  induction x with
  | nil => exact ⟨rfl,Nat.zero_le _⟩
  | cons b x ih =>
    simp only [countedBinaryDivide,List.length_cons,ih.1]
    exact ⟨True.intro,List.length_take_le _ _⟩

theorem countedBinaryDivide_spec (d : ℕ) (x y : List Bool)
    (hy : y.length ≤ d) (hy0 : 0 < binaryWordValue y) :
    let q := countedBinaryDivide d y x
    binaryWordValue x = binaryWordValue q.1.1*binaryWordValue y+binaryWordValue q.1.2 ∧
      binaryWordValue q.1.2 < binaryWordValue y := by
  induction x with
  | nil => simp [countedBinaryDivide,binaryWordValue,hy0]
  | cons b x ih =>
    let p := countedBinaryDivide d y x
    let s := b :: p.1.2
    let c := countedBinarySubtract (d+1) s y false
    have hs : s.length ≤ d+1 := Nat.add_le_add_right (countedBinaryDivide_lengths d x y).2 1
    have hV := countedBinarySubtract_value (d+1) s y false hs (hy.trans (Nat.le_succ _))
    have hC := countedBinarySubtract_borrow_iff (d+1) s y false hs (hy.trans (Nat.le_succ _))
    have hY : binaryWordValue y < 2^d := (binaryWordValue_lt_pow y).trans_le
      (Nat.pow_le_pow_right (by decide) hy)
    have hS : binaryWordValue s = bitDigit b+2*binaryWordValue p.1.2 := rfl
    have hb := bitDigit_le_one b
    have h0 : bitDigit false = 0 := rfl
    have h1 : bitDigit true = 1 := rfl
    have hP : binaryWordValue x = binaryWordValue p.1.1*binaryWordValue y+binaryWordValue p.1.2 := ih.1
    have hR : binaryWordValue p.1.2 < binaryWordValue y := ih.2
    change c.1.2 = true ↔ binaryWordValue s < binaryWordValue y+bitDigit false at hC
    change binaryWordValue s+2^(d+1)*bitDigit c.1.2 =
      binaryWordValue y+bitDigit false+binaryWordValue c.1.1 at hV
    change binaryWordValue (b::x) = binaryWordValue ((!c.1.2)::p.1.1)*binaryWordValue y+
        binaryWordValue ((if c.1.2 then s else c.1.1).take d) ∧
      binaryWordValue ((if c.1.2 then s else c.1.1).take d) < binaryWordValue y
    by_cases he : c.1.2 = true
    · have ht : binaryWordValue s < binaryWordValue y := by simpa [bitDigit] using hC.mp he
      simp only [he, if_true, binaryWordValue_take_of_lt s d (ht.trans hY), Bool.not_true, binaryWordValue, h0, zero_add]
      refine ⟨?_,ht⟩
      nlinarith
    · have he' : c.1.2 = false := Bool.eq_false_iff.mpr he
      have ht : binaryWordValue c.1.1 < binaryWordValue y := by
        simp only [he',h0,mul_zero,add_zero] at hV
        omega
      simp only [he', Bool.false_eq_true, if_false, binaryWordValue_take_of_lt c.1.1 d (ht.trans hY),
        Bool.not_false, binaryWordValue, h1]
      refine ⟨?_,ht⟩
      simp only [he',h0,mul_zero,add_zero] at hV
      nlinarith

theorem countedBinaryDivide_value (d : ℕ) (x y : List Bool) (hy : y.length ≤ d)
    (hy0 : 0 < binaryWordValue y) :
    let q := countedBinaryDivide d y x
    binaryWordValue q.1.1 = binaryWordValue x / binaryWordValue y ∧
      binaryWordValue q.1.2 = binaryWordValue x % binaryWordValue y := by
  let q := countedBinaryDivide d y x
  have h := countedBinaryDivide_spec d x y hy hy0
  have hV : binaryWordValue x = binaryWordValue q.1.1*binaryWordValue y+binaryWordValue q.1.2 := h.1
  have hR : binaryWordValue q.1.2 < binaryWordValue y := h.2
  have hd : binaryWordValue x / binaryWordValue y = binaryWordValue q.1.1 :=
    Nat.div_eq_of_lt_le (by omega) (by
      rw [Nat.add_mul,Nat.one_mul]
      omega)
  refine ⟨hd.symm,?_⟩
  have hMod := Nat.div_add_mod (binaryWordValue x) (binaryWordValue y)
  rw [hd, Nat.mul_comm] at hMod
  change binaryWordValue q.1.2 = binaryWordValue x % binaryWordValue y
  omega

lemma countedBinaryDivide_work (d : ℕ) (x y : List Bool) :
    (countedBinaryDivide d y x).2 = (16*d+23)*x.length+1 := by
  induction x with
  | nil => simp [countedBinaryDivide]
  | cons b x ih =>
    simp only [countedBinaryDivide, countedBinarySubtract_work, List.length_cons, ih]
    ring

end ProphetSecretary.Analysis
