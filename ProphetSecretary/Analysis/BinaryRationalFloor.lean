import ProphetSecretary.Analysis.BinaryFraction

/-!
# The nonnegative part of a rational floor

The dyadic mixture uses an integer floor of a scaled rational. A negative
numerator gives zero after conversion to a natural; otherwise binary long
division computes the quotient of the stored numerator and denominator.
-/

namespace ProphetSecretary.Analysis

def countedRationalFloorBits (x : ℚ) : List Bool × ℕ :=
  if x.num≤0 then ([],3) else
    let a := x.num.natAbs.bits
    let b := x.den.bits
    let d := max a.length b.length
    let q := countedBinaryDivide d b a
    (q.1.1,q.2+6*(a.length+b.length)+5)

lemma countedRationalFloorBits_value (x : ℚ) :
    binaryWordValue (countedRationalFloorBits x).1 = x.floor.toNat := by
  by_cases h : x.num≤0
  · rw [countedRationalFloorBits,if_pos h,Rat.floor_def]
    exact (Int.toNat_eq_zero.mpr (Int.ediv_nonpos_of_nonpos_of_neg h (by exact_mod_cast x.pos))).symm
  · let a := x.num.natAbs.bits
    let b := x.den.bits
    let d := max a.length b.length
    have hb : 0<binaryWordValue b := by rw [show b=x.den.bits from rfl,binaryWordValue_bits]; exact x.pos
    have hd := (countedBinaryDivide_value d a b (le_max_right _ _) hb).1
    rw [countedRationalFloorBits,if_neg h]
    change binaryWordValue (countedBinaryDivide d b a).1.1 = _
    rw [hd,show a=x.num.natAbs.bits from rfl,show b=x.den.bits from rfl,binaryWordValue_bits,binaryWordValue_bits,
      Rat.floor_def,← Int.ofNat_natAbs_of_nonneg (le_of_lt (lt_of_not_ge h)),Int.ofNat_ediv_ofNat]
    rfl

theorem countedRationalFloorBits_work (x : ℚ) (B : ℕ) (hx : RationalHeight x B) :
    (countedRationalFloorBits x).2 ≤ 60*(B+2)^2 := by
  have hW (n : ℕ) (h : n≤2^B) : n.bits.length≤B+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hp : 0 < (2:ℕ)^B := by positivity
    omega
  by_cases h : x.num≤0
  · rw [countedRationalFloorBits,if_pos h]
    change (3:ℕ)≤60*(B+2)^2
    exact (by decide : (3:ℕ)≤60).trans (Nat.le_mul_of_pos_right _ (by positivity))
  · let a := x.num.natAbs.bits
    let b := x.den.bits
    let d := max a.length b.length
    have ha : a.length≤B+1 := hW _ hx.1
    have hb : b.length≤B+1 := hW _ hx.2
    have hd : d≤B+1 := max_le ha hb
    rw [countedRationalFloorBits,if_neg h]
    change (countedBinaryDivide d b a).2+6*(a.length+b.length)+5 ≤ _
    rw [countedBinaryDivide_work]
    have hQ := Nat.mul_le_mul (show 16*d+23≤16*(B+1)+23 by omega) ha
    nlinarith [Nat.zero_le (B^2)]

end ProphetSecretary.Analysis
