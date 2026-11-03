import ProphetSecretary.Statistics.BinaryLearnerStartup

/-!
# Computing the public coefficient grid

Binary long division computes the ceiling of the scaled coefficient
interval. The resulting integer is the number of subintervals used in
the measured calibration.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

private def binaryGridExpr (m z : BinaryRational) : CalibrationBinaryExpr :=
  .node .mul (.atom m) (.node .sub (.atom (BinaryRational.ofRat (1/4))) (.atom z))

private def binaryCeil (x : BinaryRational) : ℕ × ℕ :=
  if x.storage.negative then (0,2) else
    let a := x.storage.numerator
    let b := x.storage.denominator
    let d := max a.length b.length
    let q := countedBinaryDivide d b a
    let k := binaryWordValue q.1.1
    let r := q.1.2.any id
    (if r then k+1 else k,q.2+30*(d+2)^2)

def countedBinaryPublicGrid (m : ℕ) (z : BinaryRational) : ℕ × ℕ :=
  let M := countedCalibrationNat m
  let e := (binaryGridExpr M.1 z).evaluate
  let q := binaryCeil e.1
  (q.1,M.2+e.2+q.2+3)

private lemma word_pos_iff_any (a : List Bool) : 0<binaryWordValue a ↔ a.any id=true := by
  induction a with
  | nil => simp [binaryWordValue]
  | cons b a ih =>
    cases b
    · simp [binaryWordValue,bitDigit,ih]
    · simp [binaryWordValue,bitDigit]

private lemma binaryCeil_value (x : BinaryRational) :
    (binaryCeil x).1 = (Rat.ceil x.value).toNat := by
  let a := x.storage.numerator
  let b := x.storage.denominator
  let d := max a.length b.length
  have hs := x.canonical
  have hs' : x.storage = BinaryFraction.encode x.value := hs
  have ha : binaryWordValue a=x.value.num.natAbs := by simp [a,hs',BinaryFraction.encode,binaryWordValue_bits]
  have hb : binaryWordValue b=x.value.den := by simp [b,hs',BinaryFraction.encode,binaryWordValue_bits]
  have he : x.storage.negative=decide (x.value.num<0) := by simp [hs',BinaryFraction.encode]
  rw [Rat.ceil_eq_neg_floor_neg]
  change _ = (-⌊-x.value⌋).toNat
  rw [Int.floor_neg,neg_neg]
  by_cases hn : x.value.num<0
  · rw [binaryCeil,he,if_pos (decide_eq_true hn)]
    have hh : x.value≤0 := le_of_lt (Rat.num_neg.mp hn)
    have h0 : ⌈x.value⌉≤0 := Int.ceil_nonpos.mpr hh
    exact (Int.toNat_eq_zero.mpr h0).symm
  · have hnum : (x.value.num.natAbs : ℤ)=x.value.num := Int.natAbs_of_nonneg (le_of_not_gt hn)
    have hb0 : 0<binaryWordValue b := hb.symm ▸ x.value.pos
    let q := countedBinaryDivide d b a
    let k := binaryWordValue q.1.1
    let r := binaryWordValue q.1.2
    have hq := countedBinaryDivide_spec d a b (le_max_right _ _) hb0
    change binaryWordValue a=k*binaryWordValue b+r ∧ r<binaryWordValue b at hq
    rw [ha,hb] at hq
    have hN : (x.value.num : ℚ)=(k : ℚ)*(x.value.den : ℚ)+(r : ℚ) := by
      have h := congrArg (fun j : ℕ => (j : ℤ)) hq.1
      rw [hnum,Nat.cast_add,Nat.cast_mul] at h
      exact_mod_cast h
    have hD : (0 : ℚ)<x.value.den := by exact_mod_cast x.value.pos
    have hR : (r : ℚ)<x.value.den := by exact_mod_cast hq.2
    have hQ : x.value=(k : ℚ)+(r : ℚ)/(x.value.den : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den x.value]
      rw [hN,add_div,mul_div_cancel_right₀ _ hD.ne']
    have hh : (r : ℚ)/(x.value.den : ℚ)<1 := (div_lt_one hD).2 hR
    rw [binaryCeil,he,if_neg (by simp [hn])]
    change (if q.1.2.any id then k+1 else k)=(⌈x.value⌉ : ℤ).toNat
    by_cases hr : 0<r
    · rw [if_pos ((word_pos_iff_any _).1 hr)]
      have hr' : 0<(r : ℚ)/(x.value.den : ℚ) := div_pos (by exact_mod_cast hr) hD
      have hc : ⌈x.value⌉=(k+1 : ℕ) := Int.ceil_eq_iff.mpr (by push_cast; rw [hQ]; constructor <;> linarith only [hr',hh])
      rw [hc]
      simp
    · rw [if_neg (fun h => hr ((word_pos_iff_any _).2 h))]
      have hr0 : r=0 := Nat.eq_zero_of_not_pos hr
      have hv : x.value=(k : ℚ) := by simpa [hr0] using hQ
      change k=(⌈x.value⌉ : ℤ).toNat
      rw [hv,Int.ceil_natCast]
      simp

lemma countedBinaryPublicGrid_value (m : ℕ) (z : BinaryRational) :
    (countedBinaryPublicGrid m z).1=rationalFamilyGridSize m z.value (1/4) := by
  unfold countedBinaryPublicGrid rationalFamilyGridSize
  dsimp only
  rw [binaryCeil_value,CalibrationBinaryExpr.evaluate_value]
  simp [binaryGridExpr,CalibrationBinaryExpr.value,rationalCalibrationOp,countedCalibrationNat_value,
    BinaryRational.ofRat_value]

private lemma binaryCeil_work (x : BinaryRational) (B : ℕ) (hx : RationalHeight x.value B) :
    (binaryCeil x).2≤60*(B+3)^2 := by
  have hW (n : ℕ) (h : n≤2^B) : n.bits.length≤B+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hp : 0 < (2:ℕ)^B := by positivity
    omega
  have hs : x.storage = BinaryFraction.encode x.value := x.canonical
  have ha : x.storage.numerator.length≤B+1 := by
    rw [hs]; exact hW _ hx.1
  have hb : x.storage.denominator.length≤B+1 := by
    rw [hs]; exact hW _ hx.2
  unfold binaryCeil
  split
  · nlinarith [Nat.zero_le (B^2)]
  · dsimp only
    rw [countedBinaryDivide_work]
    have hd := max_le ha hb
    have hQ := Nat.mul_le_mul (show 16*max x.storage.numerator.length x.storage.denominator.length+23≤16*(B+1)+23 by omega) ha
    have hS : (max x.storage.numerator.length x.storage.denominator.length+2)^2≤(B+3)^2 :=
      Nat.pow_le_pow_left (by omega) _
    nlinarith only [hQ,hS,Nat.zero_le (B^2)]

def binaryPublicGridWork (B : ℕ) : ℕ :=
  6*(B+2)+5*CalibrationBinaryExpr.workUnit 5 B+60*(5*(B+1)+3)^2+3

theorem countedBinaryPublicGrid_work (m D : ℕ) (z : BinaryRational) (hz : RationalHeight z.value D) :
    (countedBinaryPublicGrid m z).2≤binaryPublicGridWork (m+D+2) := by
  let B := m+D+2
  let M := countedCalibrationNat m
  let e := binaryGridExpr M.1 z
  have hm : m≤2^B := (Nat.lt_two_pow_self (n := m)).le.trans (Nat.pow_le_pow_right (by decide) (by unfold B; omega))
  have hE : e.leavesFit B := by
    refine ⟨?_,?_,hz.mono (by unfold B; omega)⟩
    · change RationalHeight M.1.value B
      rw [countedCalibrationNat_value]
      exact rationalHeight_natCast m B hm
    · change RationalHeight (BinaryRational.ofRat (1/4)).value B
      rw [BinaryRational.ofRat_value]
      exact (rationalHeight_one.div (rationalHeight_natCast 4 2 (by decide))).mono (by unfold B; omega)
  have hL : e.size=5 := rfl
  have hV := e.value_height B hE
  rw [hL,← CalibrationBinaryExpr.evaluate_value] at hV
  have hw := e.evaluate_work 5 B hE (by rw [hL])
  rw [hL] at hw
  have hc := binaryCeil_work e.evaluate.1 (5*(B+1)) hV
  have hn := countedCalibrationNat_work m B hm
  unfold binaryPublicGridWork
  change M.2+e.evaluate.2+(binaryCeil e.evaluate.1).2+3≤_
  change M.2+e.evaluate.2+(binaryCeil e.evaluate.1).2+3≤
    6*(B+2)+5*CalibrationBinaryExpr.workUnit 5 B+60*(5*(B+1)+3)^2+3
  change M.2≤_ at hn
  omega

/-- Compute the public sample scale from encoded accuracy, counting the
encoding of the fixed integer, rational division and binary ceiling. -/
def countedBinaryAccuracyScale (D : ℕ) (eps : BinaryRational) : ℕ × ℕ :=
  let d := countedCalibrationNat D
  let q := BinaryRational.countedOperation .div d.1 eps
  let m := binaryCeil q.1
  (m.1,d.2+q.2+m.2+3)

theorem countedBinaryAccuracyScale_value (D : ℕ) (eps : BinaryRational) :
    (countedBinaryAccuracyScale D eps).1=⌈(D : ℝ)/(eps.value : ℝ)⌉₊ := by
  let d := countedCalibrationNat D
  let q := BinaryRational.countedOperation .div d.1 eps
  have hq : q.1.value = (D : ℚ)/eps.value := by
    change (BinaryRational.countedOperation .div d.1 eps).1.value = _
    rw [countedCalibrationOp_value]
    change d.1.value / eps.value = _
    rw [countedCalibrationNat_value]
  change (binaryCeil q.1).1=_
  rw [binaryCeil_value,hq]
  rw [← Int.ceil_toNat]
  congr 1
  rw [Rat.ceil_eq_neg_floor_neg]
  change ⌈(D : ℚ)/eps.value⌉=_
  simpa only [Rat.cast_div,Rat.cast_natCast,Rat.ceil_cast] using
    (Rat.ceil_cast (α := ℝ) ((D : ℚ)/eps.value)).symm

/-- For a fixed integer scale the front end costs polynomially many
bit operations in the input width, before any samples are requested. -/
def binaryAccuracyScaleWork (D B : ℕ) : ℕ :=
  6*(D+B+2)+3600*(D+B+2)^3+60*(D+B+3)^2+3

theorem countedBinaryAccuracyScale_work (D B : ℕ) (eps : BinaryRational)
    (heps : RationalHeight eps.value B) :
    (countedBinaryAccuracyScale D eps).2≤binaryAccuracyScaleWork D B := by
  let d := countedCalibrationNat D
  let q := BinaryRational.countedOperation .div d.1 eps
  have hn : D≤2^D := (Nat.lt_two_pow_self (n := D)).le
  have hd : RationalHeight d.1.value D := by
    rw [countedCalibrationNat_value]
    exact rationalHeight_natCast D D hn
  have hq : RationalHeight q.1.value (D+B) := by
    change RationalHeight (BinaryRational.countedOperation .div d.1 eps).1.value (D+B)
    rw [countedCalibrationOp_value]
    exact hd.div heps
  have h₁ := countedCalibrationNat_work D D hn
  have h₂ := BinaryRational.countedOperation_work .div d.1 eps (D+B)
    (hd.mono (by omega)) (heps.mono (by omega))
  have h₃ := binaryCeil_work q.1 (D+B) hq
  have h₄ : 3*(D+1)+3≤6*(D+B+2) := by omega
  change d.2+q.2+(binaryCeil q.1).2+3≤_
  change d.2≤3*(D+1)+3 at h₁
  change q.2≤_ at h₂
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (h₁.trans h₄) h₂) h₃) _

end ProphetSecretary.Statistics.Calibration
