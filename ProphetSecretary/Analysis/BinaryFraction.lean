import ProphetSecretary.Analysis.BinaryGCD
import ProphetSecretary.Analysis.RationalHeight

/-!
# Counted normalization of a binary fraction

The unsigned numerator and positive denominator are divided by their gcd.
Trimming padded words makes the output lengths those of the canonical
rational numerator and denominator. Signs are stored separately.
-/

namespace ProphetSecretary.Analysis

def countedTrimBinaryWord : List Bool → List Bool × ℕ
  | [] => ([],1)
  | b :: x =>
    let t := countedTrimBinaryWord x
    (if !b && t.1.isEmpty then [] else b::t.1,t.2+5)

lemma countedTrimBinaryWord_value (x : List Bool) :
    (countedTrimBinaryWord x).1 = (binaryWordValue x).bits := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    let a := binaryWordValue x
    have hbit : Nat.bit b a = binaryWordValue (b::x) := by
      rw [Nat.bit_val]
      cases b <;> simp [bitDigit,binaryWordValue,a,Nat.add_comm]
    simp only [countedTrimBinaryWord,ih,← hbit]
    by_cases h : Nat.bit b a = 0
    · have h0 : a = 0 := by
        rw [Nat.bit_val] at h
        omega
      have hb : b = false := by cases b <;> simp [Nat.bit_val,h0] at h ⊢
      simp [hb,h0,a] at *
    · have hPos : a = 0 → b = true := by
        intro ha
        by_contra! hb
        have hb' := Bool.eq_false_iff.mpr hb
        exact h (by simp [Nat.bit_val,ha,hb'])
      rw [Nat.bits_append_bit _ _ hPos]
      cases b
      · have ha : a ≠ 0 := by intro he; exact h (by simp [he,Nat.bit_val])
        have hn : a.bits ≠ [] := by
          intro he
          have hv := binaryWordValue_bits a
          rw [he,binaryWordValue] at hv
          exact ha hv.symm
        have hE : a.bits.isEmpty = false := List.isEmpty_eq_false_iff.mpr hn
        change (if (!false && a.bits.isEmpty) then [] else false::a.bits) = false::a.bits
        simp [hE]
      · simp [a]

lemma countedTrimBinaryWord_work (x : List Bool) : (countedTrimBinaryWord x).2 = 5*x.length+1 := by
  induction x with
  | nil => decide
  | cons b x ih => simp only [countedTrimBinaryWord, List.length_cons, ih]; omega

structure BinaryFraction where
  negative : Bool
  numerator : List Bool
  denominator : List Bool

namespace BinaryFraction

def value (q : BinaryFraction) : ℚ :=
  let n := (binaryWordValue q.numerator : ℚ)
  (if q.negative then -n else n) / (binaryWordValue q.denominator : ℚ)

def width (q : BinaryFraction) : ℕ := max q.numerator.length q.denominator.length

def countedReduce (q : BinaryFraction) : BinaryFraction × ℕ :=
  let d := q.width
  let g := countedBinaryGCD d d q.numerator q.denominator
  let n := countedBinaryDivide d g.1 q.numerator
  let a := countedBinaryDivide d g.1 q.denominator
  let n' := countedTrimBinaryWord n.1.1
  let a' := countedTrimBinaryWord a.1.1
  (⟨q.negative,n'.1,a'.1⟩,g.2+n.2+a.2+n'.2+a'.2+4*d+8)

lemma countedReduce_value_components (q : BinaryFraction) (hq : 0 < binaryWordValue q.denominator) :
    let n := binaryWordValue q.numerator
    let a := binaryWordValue q.denominator
    let g := n.gcd a
    (q.countedReduce.1).numerator = (n/g).bits ∧
      (q.countedReduce.1).denominator = (a/g).bits := by
  let d := q.width
  let g := countedBinaryGCD d d q.numerator q.denominator
  have hd : q.denominator.length ≤ d := le_max_right _ _
  have hn : q.numerator.length ≤ d := le_max_left _ _
  have hg : binaryWordValue g.1 = (binaryWordValue q.numerator).gcd (binaryWordValue q.denominator) :=
    countedBinaryGCD_value d d _ _ hn hd ((binaryWordValue_lt_pow _).trans_le
      (Nat.pow_le_pow_right (by decide) hd))
  have hg' : 0 < binaryWordValue g.1 := hg.symm ▸ Nat.gcd_pos_of_pos_right _ hq
  have hL : g.1.length ≤ d := countedBinaryGCD_lengths d d _ _ hn hd
  have h1 := (countedBinaryDivide_value d q.numerator g.1 hL hg').1
  have h2 := (countedBinaryDivide_value d q.denominator g.1 hL hg').1
  constructor
  · change (countedTrimBinaryWord (countedBinaryDivide d g.1 q.numerator).1.1).1 = _
    rw [countedTrimBinaryWord_value,h1,hg]
  · change (countedTrimBinaryWord (countedBinaryDivide d g.1 q.denominator).1.1).1 = _
    rw [countedTrimBinaryWord_value,h2,hg]

theorem countedReduce_correct (q : BinaryFraction) (hq : 0 < binaryWordValue q.denominator) :
    (q.countedReduce.1).value = q.value ∧ 0 < binaryWordValue (q.countedReduce.1).denominator := by
  let n := binaryWordValue q.numerator
  let d := binaryWordValue q.denominator
  let g := n.gcd d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right n hq
  have hD : 0 < d/g := Nat.div_gcd_pos_of_pos_right n hq
  have h := countedReduce_value_components q hq
  have hN : binaryWordValue q.countedReduce.1.numerator = n/g := by rw [h.1,binaryWordValue_bits]
  have hDen : binaryWordValue q.countedReduce.1.denominator = d/g := by rw [h.2,binaryWordValue_bits]
  have hn : ((n/g:ℕ):ℚ)*(g:ℚ) = n := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left n d)
  have hd : ((d/g:ℕ):ℚ)*(g:ℚ) = d := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right n d)
  refine ⟨?_,hDen.symm ▸ hD⟩
  have hsign : q.countedReduce.1.negative = q.negative := rfl
  rw [value,value,hN,hDen,hsign]
  change (if q.negative then -((n/g:ℕ):ℚ) else ((n/g:ℕ):ℚ))/((d/g:ℕ):ℚ) =
    (if q.negative then -(n:ℚ) else (n:ℚ))/(d:ℚ)
  rw [← hn,← hd]
  have hG : (g:ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  cases q.negative <;> simp only [Bool.false_eq_true, if_false, if_true] <;> field_simp

theorem countedReduce_work (q : BinaryFraction) :
    q.countedReduce.2 ≤ 100*(q.width+1)^3 := by
  let d := q.width
  let g := countedBinaryGCD d d q.numerator q.denominator
  let n := countedBinaryDivide d g.1 q.numerator
  let a := countedBinaryDivide d g.1 q.denominator
  have hn : q.numerator.length ≤ d := le_max_left _ _
  have ha : q.denominator.length ≤ d := le_max_right _ _
  have hG := countedBinaryGCD_work d d _ _ hn ha
  have hN : n.2 ≤ (16*d+23)*d+1 := by
    dsimp [n]
    rw [countedBinaryDivide_work]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _
  have hA : a.2 ≤ (16*d+23)*d+1 := by
    dsimp [a]
    rw [countedBinaryDivide_work]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ ha) _
  have hNL : n.1.1.length ≤ d := (countedBinaryDivide_lengths d q.numerator g.1).1.trans_le hn
  have hAL : a.1.1.length ≤ d := (countedBinaryDivide_lengths d q.denominator g.1).1.trans_le ha
  change g.2+n.2+a.2+(countedTrimBinaryWord n.1.1).2+(countedTrimBinaryWord a.1.1).2+4*d+8 ≤ _
  rw [countedTrimBinaryWord_work,countedTrimBinaryWord_work]
  change g.2 ≤ 1+d*(40*(d+1)^2) at hG
  change _ ≤ 100*(d+1)^3
  nlinarith [Nat.zero_le (d^2),Nat.zero_le (d^3)]

theorem countedReduce_width (q : BinaryFraction) (hq : 0 < binaryWordValue q.denominator)
    {B : ℕ} (hB : RationalHeight q.value B) : q.countedReduce.1.width ≤ B+1 := by
  let o := q.countedReduce.1
  let n := binaryWordValue o.numerator
  let d := binaryWordValue o.denominator
  let z : ℤ := if o.negative then -(n:ℤ) else (n:ℤ)
  have hc := countedReduce_value_components q hq
  have hn : n = binaryWordValue q.numerator / (binaryWordValue q.numerator).gcd (binaryWordValue q.denominator) := by
    dsimp [n,o]
    rw [hc.1,binaryWordValue_bits]
  have hd : d = binaryWordValue q.denominator / (binaryWordValue q.numerator).gcd (binaryWordValue q.denominator) := by
    dsimp [d,o]
    rw [hc.2,binaryWordValue_bits]
  have hD : 0 < d := (countedReduce_correct q hq).2
  have hAbs : z.natAbs = n := by cases hs : o.negative <;> simp [z,hs]
  have hCop : Nat.Coprime z.natAbs (d:ℤ).natAbs := by
    rw [hAbs,Int.natAbs_natCast,hn,hd]
    exact Nat.gcd_div_gcd_div_gcd_of_pos_right hq
  have hVal : (z:ℚ)/(d:ℤ) = q.value := by
    rw [← (countedReduce_correct q hq).1]
    change (z:ℚ)/(d:ℤ) = o.value
    cases he : o.negative <;> simp [z,he,value,n,d]
  have hNum := Rat.num_div_eq_of_coprime (by exact_mod_cast hD : (0:ℤ) < d) hCop
  have hDen := Rat.den_div_eq_of_coprime (by exact_mod_cast hD : (0:ℤ) < d) hCop
  rw [hVal] at hNum hDen
  have hBn : n ≤ 2^B := by rw [← hAbs, ← hNum]; exact hB.1
  have hDen' : q.value.den = d := by exact_mod_cast hDen
  have hBd : d ≤ 2^B := hDen' ▸ hB.2
  have hSize (k : ℕ) (hk : k ≤ 2^B) : k.bits.length ≤ B+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hpow : 0 < (2:ℕ)^B := by positivity
    omega
  change max o.numerator.length o.denominator.length ≤ B+1
  apply max_le
  · change q.countedReduce.1.numerator.length ≤ _
    rw [hc.1,← hn]
    exact hSize n hBn
  · change q.countedReduce.1.denominator.length ≤ _
    rw [hc.2,← hd]
    exact hSize d hBd

end BinaryFraction

end ProphetSecretary.Analysis
