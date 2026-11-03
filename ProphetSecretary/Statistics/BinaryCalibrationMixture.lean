import ProphetSecretary.Statistics.BinaryCalibrationPrimitive
import ProphetSecretary.Statistics.RationalCalibrationGrid

/-!
# Binary mixture rounding

After scaling the mixture by the grid size, long division obtains the
nonnegative floor. The final comparison is between two integer words;
no rational division by the grid size is needed.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

def countedCalibrationFloor (x : CalibrationBinary) : List Bool×ℕ :=
  if x.storage.negative then ([],3) else
    let a := x.storage.numerator
    let b := x.storage.denominator
    let d := max a.length b.length
    let q := countedBinaryDivide d b a
    (q.1.1,q.2+6*(a.length+b.length)+5)

lemma countedCalibrationFloor_value (x : CalibrationBinary) :
    binaryWordValue (countedCalibrationFloor x).1=x.value.floor.toNat := by
  have hcanon : x.storage=BinaryFraction.encode x.value := x.canonical
  unfold countedCalibrationFloor
  rw [hcanon]
  dsimp only [BinaryFraction.encode]
  by_cases h : x.value.num<0
  · simp only [h,decide_true,ite_true,binaryWordValue,Rat.floor_def]
    exact (Int.toNat_eq_zero.mpr
      (Int.ediv_nonpos_of_nonpos_of_neg h.le (by exact_mod_cast x.value.pos))).symm
  · simp only [h,decide_false,Bool.false_eq_true,ite_false]
    have hh := (countedBinaryDivide_value
      (max x.value.num.natAbs.bits.length x.value.den.bits.length)
      x.value.num.natAbs.bits x.value.den.bits (le_max_right _ _)
      (by rw [binaryWordValue_bits]; exact x.value.pos)).1
    rw [hh,binaryWordValue_bits,binaryWordValue_bits,Rat.floor_def,
      ← Int.ofNat_natAbs_of_nonneg (le_of_not_gt h),Int.ofNat_ediv_ofNat]
    simp only [Int.natAbs_natCast,Int.toNat_natCast]

theorem countedCalibrationFloor_work (x : CalibrationBinary) (B : ℕ) (h : RationalHeight x.value B) :
    (countedCalibrationFloor x).2≤60*(B+2)^2 := by
  have hd := x.storage_width B h
  let a := x.storage.numerator
  let b := x.storage.denominator
  let d := max a.length b.length
  have hda : a.length≤d := le_max_left _ _
  have hdb : b.length≤d := le_max_right _ _
  change d≤B+1 at hd
  unfold countedCalibrationFloor
  split_ifs
  · exact (by decide : (3:ℕ)≤60).trans (Nat.le_mul_of_pos_right _ (by positivity))
  · change (countedBinaryDivide d b a).2+6*(a.length+b.length)+5≤_
    rw [countedBinaryDivide_work]
    have hQ := Nat.mul_le_mul (show 16*d+23≤16*(B+1)+23 by omega) (hda.trans hd)
    nlinarith [Nat.zero_le (B^2)]

def countedCalibrationWordLT (a b : List Bool) : Bool×ℕ :=
  let p := countedBinarySubtract (max a.length b.length) a b false
  (p.1.2,p.2+2)

lemma countedCalibrationWordLT_value (a b : List Bool) :
    (countedCalibrationWordLT a b).1=decide (binaryWordValue a<binaryWordValue b) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [countedCalibrationWordLT,bitDigit,Bool.false_eq_true,ite_false,Nat.add_zero,decide_eq_true_eq] using
    countedBinarySubtract_borrow_iff (max a.length b.length) a b false (le_max_left _ _) (le_max_right _ _)

lemma countedCalibrationWordLT_work (a b : List Bool) (B : ℕ)
    (ha : a.length≤B) (hb : b.length≤B) :
    (countedCalibrationWordLT a b).2≤16*B+12 := by
  have h := max_le ha hb
  simp only [countedCalibrationWordLT,countedBinarySubtract_work]
  omega

/-- The comparison uses the supplied public words for the grid size and its
largest index. The coin is already supplied as a little endian word. -/
def countedCalibrationMixture (scale alpha : CalibrationBinary) (last coin : List Bool) : Bool×ℕ :=
  let q := BinaryRational.countedOperation .mul scale alpha
  let f := countedCalibrationFloor q.1
  let c := countedCalibrationWordLT f.1 last
  let p := countedCalibrationWordLT coin (if c.1 then f.1 else last)
  (p.1,q.2+f.2+c.2+p.2+4)

lemma countedCalibrationMixture_value (scale alpha : CalibrationBinary) (last coin : List Bool)
    (N : ℕ) (hN : 0<N) (hs : scale.value=(N:ℚ)) (hl : binaryWordValue last=N-1) :
    (countedCalibrationMixture scale alpha last coin).1=
      decide ((binaryWordValue coin:ℚ)/(N:ℚ)<rationalMixtureGridRound N hN alpha.value) := by
  have hsN : (0:ℚ)<(N:ℚ) := by exact_mod_cast hN
  let q := BinaryRational.countedOperation .mul scale alpha
  let f := countedCalibrationFloor q.1
  let L := (Rat.floor ((N:ℚ)*alpha.value)).toNat
  have hF : binaryWordValue f.1=L := by
    simp only [f,q,L,countedCalibrationFloor_value,countedCalibrationOp_value,rationalCalibrationOp,hs]
  have hh : binaryWordValue (if (countedCalibrationWordLT f.1 last).1 then f.1 else last)=min (N-1) L := by
    rw [countedCalibrationWordLT_value,hF,hl]
    by_cases h : L<N-1
    · simpa only [h,decide_true,ite_true,min_eq_right h.le] using hF
    · simpa only [h,decide_false,Bool.false_eq_true,ite_false,min_eq_left (le_of_not_gt h)] using hl
  change (countedCalibrationWordLT coin (if (countedCalibrationWordLT f.1 last).1 then f.1 else last)).1=_
  rw [countedCalibrationWordLT_value,hh]
  apply decide_eq_decide.mpr
  change _ ↔ (binaryWordValue coin:ℚ)/(N:ℚ) < ((min (N-1) L : ℕ):ℚ)/(N:ℚ)
  rw [div_lt_div_iff_of_pos_right hsN]
  exact Nat.cast_lt.symm

lemma countedCalibrationFloor_length (x : CalibrationBinary) (B : ℕ) (h : RationalHeight x.value B) :
    (countedCalibrationFloor x).1.length≤B+1 := by
  have hw := x.storage_width B h
  unfold countedCalibrationFloor
  split_ifs
  · simp
  · rw [(countedBinaryDivide_lengths _ _ _).1]
    exact (le_max_left _ _).trans hw

theorem countedCalibrationMixture_work (scale alpha : CalibrationBinary) (last coin : List Bool)
    (B : ℕ) (hs : RationalHeight scale.value B) (ha : RationalHeight alpha.value B)
    (hl : last.length≤B) (hc : coin.length≤B) :
    (countedCalibrationMixture scale alpha last coin).2≤
      3600*(B+2)^3+60*(2*B+2)^2+2*(16*(2*B+1)+12)+4 := by
  let q := BinaryRational.countedOperation .mul scale alpha
  have hqW : q.2≤3600*(B+2)^3 := BinaryRational.countedOperation_work .mul _ _ B hs ha
  have hqH : RationalHeight q.1.value (2*B) := by
    simp only [q,countedCalibrationOp_value,rationalCalibrationOp]
    exact (hs.mul ha).mono (by omega)
  let f := countedCalibrationFloor q.1
  have hfW : f.2≤60*(2*B+2)^2 := countedCalibrationFloor_work _ _ hqH
  have hfL : f.1.length≤2*B+1 := countedCalibrationFloor_length _ _ hqH
  let c := countedCalibrationWordLT f.1 last
  have hcW : c.2≤16*(2*B+1)+12 :=
    countedCalibrationWordLT_work _ _ _ hfL (hl.trans (by omega))
  have hsel : (if c.1 then f.1 else last).length≤2*B+1 := by split_ifs <;> omega
  have hpW := countedCalibrationWordLT_work coin (if c.1 then f.1 else last)
    (2*B+1) (hc.trans (by omega)) hsel
  change q.2+f.2+c.2+(countedCalibrationWordLT coin (if c.1 then f.1 else last)).2+4≤_
  omega

end ProphetSecretary.Statistics.Calibration
