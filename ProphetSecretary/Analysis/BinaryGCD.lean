import ProphetSecretary.Analysis.BinaryDivision
import Mathlib.Data.Nat.Size

/-!
# Counted binary Euclidean reduction

Two successive Euclidean remainders reduce the second operand's bit width
by at least one. The executable loop uses this width as a fuel bound.
-/

namespace ProphetSecretary.Analysis

lemma binaryWordValue_eq_zero_iff_all_not (x : List Bool) :
    binaryWordValue x = 0 ↔ (x.all (! ·)) = true := by
  induction x with
  | nil => decide
  | cons b x ih =>
    cases b
    · simp only [binaryWordValue, bitDigit, Bool.false_eq_true, if_false, zero_add,
        List.all_cons, Bool.not_false, Bool.true_and, Nat.mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ih]
    · simp [binaryWordValue, bitDigit]

lemma binaryWordValue_bits (n : ℕ) : binaryWordValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h]
    simp only [binaryWordValue,ih,Nat.bit_val]
    cases b <;> simp [bitDigit,Nat.add_comm]

/-- One fuel unit performs up to two Euclidean steps. -/
def countedBinaryGCD (d : ℕ) : ℕ → List Bool → List Bool → List Bool × ℕ
  | 0,x,_ => (x,1)
  | fuel+1,x,y =>
    if y.all (! ·) then (x,2*d+2) else
    let p := countedBinaryDivide d y x
    let z := p.1.2
    if z.all (! ·) then (y,p.2+4*d+4) else
    let q := countedBinaryDivide d z y
    let g := countedBinaryGCD d fuel z q.1.2
    (g.1,g.2+p.2+q.2+4*d+8)

private lemma mod_mod_lt_pow (k a b : ℕ) (hb : 0 < b) (hb' : b < 2^(k+1))
    (hz : 0 < a%b) : b%(a%b) < 2^k := by
  let z := a%b
  have hz' : z < b := Nat.mod_lt a hb
  by_cases h : z < 2^k
  · exact (Nat.mod_lt b hz).trans h
  · change b%z < _
    rw [Nat.mod_eq_sub_mod hz'.le, Nat.mod_eq_of_lt]
    · rw [pow_succ] at hb'
      omega
    · rw [pow_succ] at hb'
      omega

private lemma gcd_mod_right (a b : ℕ) : a.gcd b = b.gcd (a%b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a%b) b]

theorem countedBinaryGCD_value (d k : ℕ) (x y : List Bool)
    (hx : x.length ≤ d) (hy : y.length ≤ d) (hk : binaryWordValue y < 2^k) :
    binaryWordValue (countedBinaryGCD d k x y).1 = (binaryWordValue x).gcd (binaryWordValue y) := by
  induction k generalizing x y with
  | zero =>
    have he : binaryWordValue y = 0 := by simpa using hk
    simp [countedBinaryGCD,he]
  | succ k ih =>
    by_cases hy' : y.all (! ·) = true
    · have he := (binaryWordValue_eq_zero_iff_all_not y).mpr hy'
      simp [countedBinaryGCD,hy',he]
    · have hy0 : 0 < binaryWordValue y := Nat.pos_of_ne_zero (mt (binaryWordValue_eq_zero_iff_all_not y).mp hy')
      let p := countedBinaryDivide d y x
      let z := p.1.2
      have hz : z.length ≤ d := (countedBinaryDivide_lengths d x y).2
      have hZ : binaryWordValue z = binaryWordValue x % binaryWordValue y :=
        (countedBinaryDivide_value d x y hy hy0).2
      by_cases hz' : z.all (! ·) = true
      · have he := (binaryWordValue_eq_zero_iff_all_not z).mpr hz'
        rw [gcd_mod_right, ← hZ, he, Nat.gcd_zero_right]
        rw [countedBinaryGCD, if_neg hy', if_pos
          (show (countedBinaryDivide d y x).1.2.all (! ·) = true from hz')]
      · have hz0 : 0 < binaryWordValue z := Nat.pos_of_ne_zero (mt (binaryWordValue_eq_zero_iff_all_not z).mp hz')
        let q := countedBinaryDivide d z y
        let w := q.1.2
        have hw : w.length ≤ d := (countedBinaryDivide_lengths d y z).2
        have hW : binaryWordValue w = binaryWordValue y % binaryWordValue z :=
          (countedBinaryDivide_value d y z hz hz0).2
        have hk' : binaryWordValue w < 2^k := by
          rw [hW,hZ]
          exact mod_mod_lt_pow k (binaryWordValue x) (binaryWordValue y) hy0 hk (hZ ▸ hz0)
        rw [countedBinaryGCD, if_neg hy', if_neg
          (show ¬(countedBinaryDivide d y x).1.2.all (! ·) = true from hz')]
        change binaryWordValue (countedBinaryGCD d k z w).1 = _
        rw [ih z w hz hw hk',hW,hZ,← gcd_mod_right,← gcd_mod_right]

theorem countedBinaryGCD_lengths (d k : ℕ) (x y : List Bool) (hx : x.length ≤ d) (hy : y.length ≤ d) :
    (countedBinaryGCD d k x y).1.length ≤ d := by
  induction k generalizing x y with
  | zero => exact hx
  | succ k ih =>
    simp only [countedBinaryGCD]
    split_ifs
    · exact hx
    · exact hy
    · exact ih _ _ (countedBinaryDivide_lengths d x y).2 (countedBinaryDivide_lengths d y _).2

theorem countedBinaryGCD_work (d k : ℕ) (x y : List Bool) (hx : x.length ≤ d) (hy : y.length ≤ d) :
    (countedBinaryGCD d k x y).2 ≤ 1+k*(40*(d+1)^2) := by
  induction k generalizing x y with
  | zero => simp [countedBinaryGCD]
  | succ k ih =>
    let p := countedBinaryDivide d y x
    let z := p.1.2
    let q := countedBinaryDivide d z y
    let w := q.1.2
    have hp : p.2 ≤ (16*d+23)*d+1 := by
      dsimp [p]
      rw [countedBinaryDivide_work]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hx) _
    have hq : q.2 ≤ (16*d+23)*d+1 := by
      dsimp [q]
      rw [countedBinaryDivide_work]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hy) _
    have hg := ih z w (countedBinaryDivide_lengths d x y).2 (countedBinaryDivide_lengths d y z).2
    simp only [countedBinaryGCD]
    split_ifs
    · nlinarith [Nat.zero_le (d^2),Nat.zero_le (k*(40*(d+1)^2))]
    · change p.2+4*d+4 ≤ _
      nlinarith [Nat.zero_le (d^2),Nat.zero_le (k*(40*(d+1)^2))]
    · change (countedBinaryGCD d k z w).2+p.2+q.2+4*d+8 ≤ _
      nlinarith [Nat.zero_le (d^2)]

end ProphetSecretary.Analysis
