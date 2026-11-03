import ProphetSecretary.Analysis.BinaryFraction

/-!
# Counted exact rational operations

The arithmetic operates on signed binary numerators and positive binary
denominators. Addition uses cross-products, multiplication uses two products,
and division swaps the second fraction's magnitude fields. Reduction is
performed after each operation.
-/

namespace ProphetSecretary.Analysis

def signedBinaryValue (negative : Bool) (x : List Bool) : ℚ :=
  if negative then -(binaryWordValue x:ℚ) else (binaryWordValue x:ℚ)

def countedSignedBinaryAdd (sx : Bool) (x : List Bool) (sy : Bool) (y : List Bool) :
    (Bool × List Bool) × ℕ :=
  let d := max x.length y.length
  if sx = sy then
    let a := countedBinaryAdd d x y false
    ((sx,a.1),a.2+4*d+6)
  else
    let a := countedBinarySubtract d x y false
    if a.1.2 then
      let b := countedBinarySubtract d y x false
      ((sy,b.1.1),a.2+b.2+4*d+7)
    else ((sx,a.1.1),a.2+4*d+7)

lemma countedSignedBinaryAdd_value (sx : Bool) (x : List Bool) (sy : Bool) (y : List Bool) :
    let q := countedSignedBinaryAdd sx x sy y
    signedBinaryValue q.1.1 q.1.2 = signedBinaryValue sx x + signedBinaryValue sy y := by
  let d := max x.length y.length
  let a := countedBinarySubtract d x y false
  let b := countedBinarySubtract d y x false
  have hx : x.length ≤ d := le_max_left _ _
  have hy : y.length ≤ d := le_max_right _ _
  by_cases h : sx = sy
  · subst sy
    simp only [countedSignedBinaryAdd, if_true, eq_self]
    unfold signedBinaryValue
    rw [countedBinaryAdd_value d x y false hx hy]
    cases sx <;> simp [bitDigit,Nat.cast_add,add_comm]
  · have ha : a.1.2 = true ↔ binaryWordValue x < binaryWordValue y := by
      simpa [bitDigit,a] using countedBinarySubtract_borrow_iff d x y false hx hy
    have hb : b.1.2 = true ↔ binaryWordValue y < binaryWordValue x := by
      simpa [bitDigit,b] using countedBinarySubtract_borrow_iff d y x false hy hx
    by_cases ha' : a.1.2 = true
    · have hb' : b.1.2 = false := Bool.eq_false_iff.mpr (fun ht => (ha.mp ha').not_gt (hb.mp ht))
      have he : binaryWordValue y = binaryWordValue x+binaryWordValue b.1.1 := by
        have hv := countedBinarySubtract_value d y x false hy hx
        change binaryWordValue y+2^d*bitDigit b.1.2 = binaryWordValue x+bitDigit false+binaryWordValue b.1.1 at hv
        simpa [hb',bitDigit] using hv
      have he' : (binaryWordValue y:ℚ) = (binaryWordValue x:ℚ)+(binaryWordValue b.1.1:ℚ) := by exact_mod_cast he
      rw [countedSignedBinaryAdd, if_neg h, if_pos (show (countedBinarySubtract d x y false).1.2 = true from ha')]
      change signedBinaryValue sy b.1.1 = _
      cases sx <;> cases sy <;> simp_all [signedBinaryValue]
    · have ha0 : a.1.2 = false := Bool.eq_false_iff.mpr ha'
      have he : binaryWordValue x = binaryWordValue y+binaryWordValue a.1.1 := by
        have hv := countedBinarySubtract_value d x y false hx hy
        change binaryWordValue x+2^d*bitDigit a.1.2 = binaryWordValue y+bitDigit false+binaryWordValue a.1.1 at hv
        simpa [ha0,bitDigit] using hv
      have he' : (binaryWordValue x:ℚ) = (binaryWordValue y:ℚ)+(binaryWordValue a.1.1:ℚ) := by exact_mod_cast he
      rw [countedSignedBinaryAdd, if_neg h, if_neg (show ¬(countedBinarySubtract d x y false).1.2 = true from ha')]
      change signedBinaryValue sx a.1.1 = _
      cases sx <;> cases sy <;> simp_all [signedBinaryValue]

lemma countedSignedBinaryAdd_length_work (sx : Bool) (x : List Bool) (sy : Bool) (y : List Bool) :
    let q := countedSignedBinaryAdd sx x sy y
    let d := max x.length y.length
    q.1.2.length ≤ d+1 ∧ q.2 ≤ 40*(d+1) := by
  let d := max x.length y.length
  unfold countedSignedBinaryAdd
  dsimp only
  split_ifs
  · exact ⟨countedBinaryAdd_length _ _ _ _, by rw [countedBinaryAdd_work]; omega⟩
  · rw [countedBinarySubtract_length,countedBinarySubtract_work,countedBinarySubtract_work]
    omega
  · rw [countedBinarySubtract_length,countedBinarySubtract_work]
    omega

namespace BinaryFraction

def countedAdd (x y : BinaryFraction) : BinaryFraction × ℕ :=
  let a := countedBinaryMultiply x.numerator y.denominator
  let b := countedBinaryMultiply y.numerator x.denominator
  let d := countedBinaryMultiply x.denominator y.denominator
  let n := countedSignedBinaryAdd x.negative a.1 y.negative b.1
  let q := countedReduce ⟨n.1.1,n.1.2,d.1⟩
  (q.1,a.2+b.2+d.2+n.2+q.2+8)

def countedMul (x y : BinaryFraction) : BinaryFraction × ℕ :=
  let a := countedBinaryMultiply x.numerator y.numerator
  let d := countedBinaryMultiply x.denominator y.denominator
  let q := countedReduce ⟨x.negative ^^ y.negative,a.1,d.1⟩
  (q.1,a.2+d.2+q.2+6)

def neg (q : BinaryFraction) : BinaryFraction := {q with negative := !q.negative}

def countedInv (q : BinaryFraction) : BinaryFraction × ℕ :=
  if q.numerator.all (! ·) then (⟨false,[],[true]⟩,2*q.numerator.length+5)
  else (⟨q.negative,q.denominator,q.numerator⟩,2*q.numerator.length+5)

def countedSub (x y : BinaryFraction) : BinaryFraction × ℕ :=
  let q := countedAdd x y.neg
  (q.1,q.2+1)

def countedDiv (x y : BinaryFraction) : BinaryFraction × ℕ :=
  let i := countedInv y
  let q := countedMul x i.1
  (q.1,i.2+q.2+1)

lemma value_neg (q : BinaryFraction) : q.neg.value = -q.value := by
  cases h : q.negative <;> simp [neg,value,h,neg_div]

theorem countedAdd_correct (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) :
    (x.countedAdd y).1.value = x.value+y.value ∧ 0 < binaryWordValue (x.countedAdd y).1.denominator := by
  let a := countedBinaryMultiply x.numerator y.denominator
  let b := countedBinaryMultiply y.numerator x.denominator
  let d := countedBinaryMultiply x.denominator y.denominator
  let n := countedSignedBinaryAdd x.negative a.1 y.negative b.1
  let q : BinaryFraction := ⟨n.1.1,n.1.2,d.1⟩
  have hd : 0 < binaryWordValue q.denominator := by
    change 0 < binaryWordValue d.1
    rw [show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator y.denominator]
    positivity
  have h := countedReduce_correct q hd
  refine ⟨h.1.trans ?_,h.2⟩
  have hn := countedSignedBinaryAdd_value x.negative a.1 y.negative b.1
  change signedBinaryValue n.1.1 n.1.2 = _ at hn
  change signedBinaryValue n.1.1 n.1.2/(binaryWordValue d.1:ℚ) = _
  rw [hn]
  have hA : signedBinaryValue x.negative a.1 =
      signedBinaryValue x.negative x.numerator*(binaryWordValue y.denominator:ℚ) := by
    unfold signedBinaryValue
    rw [show binaryWordValue a.1 = _ from countedBinaryMultiply_value x.numerator y.denominator, Nat.cast_mul]
    cases x.negative <;> simp
  have hB : signedBinaryValue y.negative b.1 =
      signedBinaryValue y.negative y.numerator*(binaryWordValue x.denominator:ℚ) := by
    unfold signedBinaryValue
    rw [show binaryWordValue b.1 = _ from countedBinaryMultiply_value y.numerator x.denominator, Nat.cast_mul]
    cases y.negative <;> simp
  rw [hA,hB,show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator y.denominator,Nat.cast_mul]
  symm
  simpa only [value,signedBinaryValue,mul_comm (binaryWordValue x.denominator:ℚ)] using
    div_add_div (signedBinaryValue x.negative x.numerator) (signedBinaryValue y.negative y.numerator)
      (by positivity : (binaryWordValue x.denominator:ℚ) ≠ 0) (by positivity : (binaryWordValue y.denominator:ℚ) ≠ 0)

theorem countedMul_correct (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) :
    (x.countedMul y).1.value = x.value*y.value ∧ 0 < binaryWordValue (x.countedMul y).1.denominator := by
  let a := countedBinaryMultiply x.numerator y.numerator
  let d := countedBinaryMultiply x.denominator y.denominator
  let q : BinaryFraction := ⟨x.negative ^^ y.negative,a.1,d.1⟩
  have hd : 0 < binaryWordValue q.denominator := by
    change 0 < binaryWordValue d.1
    rw [show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator y.denominator]
    positivity
  have h := countedReduce_correct q hd
  refine ⟨h.1.trans ?_,h.2⟩
  change signedBinaryValue (x.negative ^^ y.negative) a.1/(binaryWordValue d.1:ℚ) = _
  rw [show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator y.denominator,Nat.cast_mul]
  unfold signedBinaryValue
  rw [show binaryWordValue a.1 = _ from countedBinaryMultiply_value x.numerator y.numerator,Nat.cast_mul]
  cases hx' : x.negative <;> cases hy' : y.negative <;> simp [value,hx',hy',div_mul_div_comm]

theorem countedInv_correct (q : BinaryFraction) (_hq : 0 < binaryWordValue q.denominator) :
    q.countedInv.1.value = q.value⁻¹ ∧ 0 < binaryWordValue q.countedInv.1.denominator := by
  by_cases h : q.numerator.all (! ·) = true
  · have he := (binaryWordValue_eq_zero_iff_all_not _).mpr h
    simp [countedInv,h,value,binaryWordValue,bitDigit,he]
  · have hp : 0 < binaryWordValue q.numerator := Nat.pos_of_ne_zero (mt (binaryWordValue_eq_zero_iff_all_not _).mp h)
    rw [countedInv,if_neg h]
    refine ⟨?_,hp⟩
    cases hs : q.negative <;> simp [value,hs,inv_div,neg_div]

theorem countedSub_correct (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) :
    (x.countedSub y).1.value = x.value-y.value ∧ 0 < binaryWordValue (x.countedSub y).1.denominator := by
  simpa only [countedSub,value_neg,sub_eq_add_neg] using countedAdd_correct x y.neg hx hy

theorem countedDiv_correct (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) :
    (x.countedDiv y).1.value = x.value/y.value ∧ 0 < binaryWordValue (x.countedDiv y).1.denominator := by
  have hi := countedInv_correct y hy
  simpa only [countedDiv,hi.1,div_eq_mul_inv] using countedMul_correct x y.countedInv.1 hx hi.2

private lemma product_width_work (x y : List Bool) (B : ℕ) (hx : x.length ≤ B) (hy : y.length ≤ B) :
    (countedBinaryMultiply x y).1.length ≤ 3*B ∧
      (countedBinaryMultiply x y).2 ≤ 96*(B+1)^2 := by
  refine ⟨(countedBinaryMultiply_length x y).trans (by omega), (countedBinaryMultiply_work x y).trans ?_⟩
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left 32 (Nat.add_le_add_right hx 1))
    (show 2*x.length+y.length+2 ≤ 3*(B+1) by omega)
  exact h.trans_eq (by ring)

theorem countedAdd_work (x y : BinaryFraction) (B : ℕ) (hx : x.width ≤ B) (hy : y.width ≤ B) :
    (x.countedAdd y).2 ≤ 3200*(B+1)^3 := by
  let a := countedBinaryMultiply x.numerator y.denominator
  let b := countedBinaryMultiply y.numerator x.denominator
  let d := countedBinaryMultiply x.denominator y.denominator
  let n := countedSignedBinaryAdd x.negative a.1 y.negative b.1
  let q : BinaryFraction := ⟨n.1.1,n.1.2,d.1⟩
  have ha := product_width_work x.numerator y.denominator B ((le_max_left _ _).trans hx) ((le_max_right _ _).trans hy)
  have hb := product_width_work y.numerator x.denominator B ((le_max_left _ _).trans hy) ((le_max_right _ _).trans hx)
  have hd := product_width_work x.denominator y.denominator B ((le_max_right _ _).trans hx) ((le_max_right _ _).trans hy)
  have hN := countedSignedBinaryAdd_length_work x.negative a.1 y.negative b.1
  have hL : max a.1.length b.1.length ≤ 3*B := max_le ha.1 hb.1
  have hn : n.2 ≤ 40*(3*B+1) := hN.2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hL 1))
  have hq : q.width ≤ 3*B+1 := max_le (hN.1.trans (Nat.add_le_add_right hL 1)) (hd.1.trans (Nat.le_succ _))
  have hq' : q.countedReduce.2 ≤ 2700*(B+1)^3 := (countedReduce_work q).trans
    ((Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (show q.width+1 ≤ 3*(B+1) by omega) 3)).trans_eq (by ring))
  change a.2+b.2+d.2+n.2+q.countedReduce.2+8 ≤ _
  have ha' : a.2 ≤ 96*(B+1)^2 := ha.2
  have hb' : b.2 ≤ 96*(B+1)^2 := hb.2
  have hd' : d.2 ≤ 96*(B+1)^2 := hd.2
  nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]

theorem countedMul_work (x y : BinaryFraction) (B : ℕ) (hx : x.width ≤ B) (hy : y.width ≤ B) :
    (x.countedMul y).2 ≤ 3100*(B+1)^3 := by
  let a := countedBinaryMultiply x.numerator y.numerator
  let d := countedBinaryMultiply x.denominator y.denominator
  let q : BinaryFraction := ⟨x.negative ^^ y.negative,a.1,d.1⟩
  have ha := product_width_work x.numerator y.numerator B ((le_max_left _ _).trans hx) ((le_max_left _ _).trans hy)
  have hd := product_width_work x.denominator y.denominator B ((le_max_right _ _).trans hx) ((le_max_right _ _).trans hy)
  have hq : q.width ≤ 3*B := max_le ha.1 hd.1
  have hq' : q.countedReduce.2 ≤ 2700*(B+1)^3 := (countedReduce_work q).trans
    ((Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (show q.width+1 ≤ 3*(B+1) by omega) 3)).trans_eq (by ring))
  change a.2+d.2+q.countedReduce.2+6 ≤ _
  have ha' : a.2 ≤ 96*(B+1)^2 := ha.2
  have hd' : d.2 ≤ 96*(B+1)^2 := hd.2
  nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]

theorem countedSub_work (x y : BinaryFraction) (B : ℕ) (hx : x.width ≤ B) (hy : y.width ≤ B) :
    (x.countedSub y).2 ≤ 3300*(B+1)^3 := by
  have h := countedAdd_work x y.neg B hx hy
  change (x.countedAdd y.neg).2+1 ≤ _
  nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]

lemma countedInv_width_work (q : BinaryFraction) (B : ℕ) (hB : 1 ≤ B) (hq : q.width ≤ B) :
    q.countedInv.1.width ≤ B ∧ q.countedInv.2 ≤ 2*B+5 := by
  have hn : q.numerator.length ≤ B := (le_max_left _ _).trans hq
  have hd : q.denominator.length ≤ B := (le_max_right _ _).trans hq
  unfold countedInv
  split_ifs
  · exact ⟨hB,by omega⟩
  · exact ⟨max_le hd hn,by omega⟩

theorem countedDiv_work (x y : BinaryFraction) (B : ℕ) (hB : 1 ≤ B) (hx : x.width ≤ B) (hy : y.width ≤ B) :
    (x.countedDiv y).2 ≤ 3300*(B+1)^3 := by
  have hi := countedInv_width_work y B hB hy
  have hm := countedMul_work x y.countedInv.1 B hx hi.1
  change y.countedInv.2+(x.countedMul y.countedInv.1).2+1 ≤ _
  nlinarith [hi.2,Nat.zero_le (B^2),Nat.zero_le (B^3)]

private lemma countedReduce_width_le_raw (q : BinaryFraction) (hq : 0 < binaryWordValue q.denominator) :
    q.countedReduce.1.width ≤ q.width := by
  have h := countedReduce_value_components q hq
  unfold width
  rw [h.1,h.2]
  apply max_le
  · rw [Nat.size_eq_bits_len,Nat.size_le]
    exact ((Nat.div_le_self _ _).trans_lt (binaryWordValue_lt_pow _)).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  · rw [Nat.size_eq_bits_len,Nat.size_le]
    exact ((Nat.div_le_self _ _).trans_lt (binaryWordValue_lt_pow _)).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

def countedLE (x y : BinaryFraction) : Bool × ℕ :=
  let q := countedSub x y
  (q.1.negative || q.1.numerator.all (! ·),q.2+2*q.1.numerator.length+4)

theorem countedLE_correct (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) :
    (x.countedLE y).1 = true ↔ x.value ≤ y.value := by
  let q := (x.countedSub y).1
  have hq := countedSub_correct x y hx hy
  change (q.negative || q.numerator.all (! ·)) = true ↔ _
  rw [← sub_nonpos, ← hq.1]
  have hd : (0:ℚ) < (binaryWordValue q.denominator:ℚ) := by exact_mod_cast hq.2
  change _ ↔ signedBinaryValue q.negative q.numerator / (binaryWordValue q.denominator:ℚ) ≤ 0
  rw [div_le_iff₀ hd,zero_mul]
  cases hs : q.negative
  · simp only [Bool.false_or,signedBinaryValue,if_false,Bool.false_eq_true,← binaryWordValue_eq_zero_iff_all_not]
    norm_cast
    exact Nat.le_zero.symm
  · simp [signedBinaryValue]

theorem countedLE_work (x y : BinaryFraction) (B : ℕ) (hx : x.width ≤ B) (hy : y.width ≤ B)
    (hxd : 0 < binaryWordValue x.denominator) (hyd : 0 < binaryWordValue y.denominator) :
    (x.countedLE y).2 ≤ 3400*(B+1)^3 := by
  let v := y.neg
  let a := countedBinaryMultiply x.numerator v.denominator
  let b := countedBinaryMultiply v.numerator x.denominator
  let d := countedBinaryMultiply x.denominator v.denominator
  let n := countedSignedBinaryAdd x.negative a.1 v.negative b.1
  let q : BinaryFraction := ⟨n.1.1,n.1.2,d.1⟩
  have hd : 0 < binaryWordValue q.denominator := by
    change 0 < binaryWordValue d.1
    rw [show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator v.denominator]
    exact Nat.mul_pos hxd hyd
  have haL := (product_width_work x.numerator v.denominator B ((le_max_left _ _).trans hx)
    ((le_max_right _ _).trans hy)).1
  have hbL := (product_width_work v.numerator x.denominator B ((le_max_left _ _).trans hy)
    ((le_max_right _ _).trans hx)).1
  have hdL := (product_width_work x.denominator v.denominator B ((le_max_right _ _).trans hx)
    ((le_max_right _ _).trans hy)).1
  have hN := (countedSignedBinaryAdd_length_work x.negative a.1 v.negative b.1).1
  have hdL' : d.1.length ≤ 3*B := hdL
  have hq : q.width ≤ 3*B+1 := max_le (hN.trans (Nat.add_le_add_right (max_le haL hbL) 1))
    (hdL'.trans (Nat.le_succ _))
  have hlen : (x.countedSub y).1.numerator.length ≤ 3*B+1 :=
    (le_max_left _ _).trans ((countedReduce_width_le_raw q hd).trans hq)
  have hSub := countedSub_work x y B hx hy
  change (x.countedSub y).2+2*(x.countedSub y).1.numerator.length+4 ≤ _
  nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]

end BinaryFraction

end ProphetSecretary.Analysis
