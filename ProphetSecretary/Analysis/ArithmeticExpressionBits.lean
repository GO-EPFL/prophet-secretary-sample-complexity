import ProphetSecretary.Analysis.ArithmeticExpressionHeight
import ProphetSecretary.Analysis.BinaryFractionOperations

/-!
# Evaluating arithmetic expressions on binary fractions

The counted evaluator uses the exact binary operations at each node.
Canonical reduction keeps the width bounded by the mathematical rational
height. Comparisons select an already computed operand.
-/

namespace ProphetSecretary.Analysis

namespace BinaryFraction

def ofInt (z : ℤ) : BinaryFraction := ⟨decide (z<0),z.natAbs.bits,[true]⟩

lemma ofInt_value (z : ℤ) : (ofInt z).value = (z:ℚ) := by
  simp only [ofInt,value,binaryWordValue_bits,show binaryWordValue [true]=1 by decide,
    Nat.cast_one,div_one,decide_eq_true_eq]
  by_cases h : z < 0
  · rw [if_pos h]
    exact_mod_cast (Int.eq_neg_natAbs_of_nonpos h.le).symm
  · rw [if_neg h]
    have he : (z.natAbs:ℤ) = z := Int.ofNat_natAbs_of_nonneg (le_of_not_gt h)
    rw [← Int.cast_natCast,he]

lemma ofInt_width (z : ℤ) (B : ℕ) (h : z.natAbs ≤ 2^B) : (ofInt z).width ≤ B+1 := by
  apply max_le
  · change z.natAbs.bits.length ≤ B+1
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hP : 0 < (2:ℕ)^B := by positivity
    omega
  · simp [ofInt]

lemma countedAdd_width (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) (B : ℕ) (hB : RationalHeight (x.value+y.value) B) :
    (x.countedAdd y).1.width ≤ B+1 := by
  let a := countedBinaryMultiply x.numerator y.denominator
  let b := countedBinaryMultiply y.numerator x.denominator
  let n := countedSignedBinaryAdd x.negative a.1 y.negative b.1
  let d := countedBinaryMultiply x.denominator y.denominator
  let q : BinaryFraction := ⟨n.1.1,n.1.2,d.1⟩
  have hd : 0 < binaryWordValue q.denominator := by
    change 0 < binaryWordValue d.1
    rw [show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator y.denominator]
    exact Nat.mul_pos hx hy
  change q.countedReduce.1.width ≤ B+1
  apply countedReduce_width q hd
  rw [← (countedReduce_correct q hd).1]
  change RationalHeight (x.countedAdd y).1.value B
  rwa [(countedAdd_correct x y hx hy).1]

lemma countedMul_width (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) (B : ℕ) (hB : RationalHeight (x.value*y.value) B) :
    (x.countedMul y).1.width ≤ B+1 := by
  let a := countedBinaryMultiply x.numerator y.numerator
  let d := countedBinaryMultiply x.denominator y.denominator
  let q : BinaryFraction := ⟨x.negative ^^ y.negative,a.1,d.1⟩
  have hd : 0 < binaryWordValue q.denominator := by
    change 0 < binaryWordValue d.1
    rw [show binaryWordValue d.1 = _ from countedBinaryMultiply_value x.denominator y.denominator]
    exact Nat.mul_pos hx hy
  change q.countedReduce.1.width ≤ B+1
  apply countedReduce_width q hd
  rw [← (countedReduce_correct q hd).1]
  change RationalHeight (x.countedMul y).1.value B
  rwa [(countedMul_correct x y hx hy).1]

lemma countedSub_width (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) (B : ℕ) (hB : RationalHeight (x.value-y.value) B) :
    (x.countedSub y).1.width ≤ B+1 := by
  apply countedAdd_width x y.neg hx hy B
  rwa [value_neg,← sub_eq_add_neg]

lemma countedDiv_width (x y : BinaryFraction) (hx : 0 < binaryWordValue x.denominator)
    (hy : 0 < binaryWordValue y.denominator) (B : ℕ) (hB : RationalHeight (x.value/y.value) B) :
    (x.countedDiv y).1.width ≤ B+1 := by
  have hi := countedInv_correct y hy
  apply countedMul_width x y.countedInv.1 hx hi.2 B
  rwa [hi.1,← div_eq_mul_inv]

inductive Operation where
  | add | sub | mul | div | minimum | maximum

def Operation.eval (op : Operation) (x y : ℚ) : ℚ := match op with
  | .add => x+y
  | .sub => x-y
  | .mul => x*y
  | .div => x/y
  | .minimum => min x y
  | .maximum => max x y

def Operation.countedEval (op : Operation) (x y : BinaryFraction) : BinaryFraction × ℕ := match op with
  | .add => x.countedAdd y
  | .sub => x.countedSub y
  | .mul => x.countedMul y
  | .div => x.countedDiv y
  | .minimum => let c := x.countedLE y; (if c.1 then x else y,c.2+2)
  | .maximum => let c := x.countedLE y; (if c.1 then y else x,c.2+2)

lemma Operation.countedEval_correct (op : Operation) (x y : BinaryFraction)
    (hx : 0 < binaryWordValue x.denominator) (hy : 0 < binaryWordValue y.denominator) :
    (op.countedEval x y).1.value = op.eval x.value y.value ∧
      0 < binaryWordValue (op.countedEval x y).1.denominator := by
  cases op
  · exact countedAdd_correct x y hx hy
  · exact countedSub_correct x y hx hy
  · exact countedMul_correct x y hx hy
  · exact countedDiv_correct x y hx hy
  · by_cases h : (x.countedLE y).1 = true
    · simp only [Operation.countedEval,Operation.eval,h,if_true,min_eq_left ((countedLE_correct x y hx hy).mp h),true_and]
      exact hx
    · simp only [Operation.countedEval,Operation.eval,if_neg h,min_eq_right (le_of_not_ge (mt (countedLE_correct x y hx hy).mpr h)),true_and]
      exact hy
  · by_cases h : (x.countedLE y).1 = true
    · simp only [Operation.countedEval,Operation.eval,h,if_true,max_eq_right ((countedLE_correct x y hx hy).mp h),true_and]
      exact hy
    · simp only [Operation.countedEval,Operation.eval,if_neg h,max_eq_left (le_of_not_ge (mt (countedLE_correct x y hx hy).mpr h)),true_and]
      exact hx

lemma Operation.countedEval_width (op : Operation) (x y : BinaryFraction)
    (hx : 0 < binaryWordValue x.denominator) (hy : 0 < binaryWordValue y.denominator)
    (B : ℕ) (hxB : x.width ≤ B+1) (hyB : y.width ≤ B+1)
    (hB : RationalHeight (op.eval x.value y.value) B) : (op.countedEval x y).1.width ≤ B+1 := by
  cases op
  · exact countedAdd_width x y hx hy B hB
  · exact countedSub_width x y hx hy B hB
  · exact countedMul_width x y hx hy B hB
  · exact countedDiv_width x y hx hy B hB
  · change (if (x.countedLE y).1 then x else y).width ≤ B+1
    split_ifs <;> assumption
  · change (if (x.countedLE y).1 then y else x).width ≤ B+1
    split_ifs <;> assumption

lemma Operation.countedEval_work (op : Operation) (x y : BinaryFraction)
    (hx : 0 < binaryWordValue x.denominator) (hy : 0 < binaryWordValue y.denominator)
    (B : ℕ) (hB : 1 ≤ B) (hxB : x.width ≤ B) (hyB : y.width ≤ B) :
    (op.countedEval x y).2 ≤ 3500*(B+1)^3 := by
  cases op
  · have h := countedAdd_work x y B hxB hyB
    exact h.trans (Nat.mul_le_mul_right _ (by decide))
  · have h := countedSub_work x y B hxB hyB
    exact h.trans (Nat.mul_le_mul_right _ (by decide))
  · have h := countedMul_work x y B hxB hyB
    exact h.trans (Nat.mul_le_mul_right _ (by decide))
  · have h := countedDiv_work x y B hB hxB hyB
    exact h.trans (Nat.mul_le_mul_right _ (by decide))
  · have h := countedLE_work x y B hxB hyB hx hy
    change (x.countedLE y).2+2 ≤ _
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]
  · have h := countedLE_work x y B hxB hyB hx hy
    change (x.countedLE y).2+2 ≤ _
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]

end BinaryFraction

namespace ArithmeticExpression

variable {ι : Type*}

private def countedBinaryNode (op : BinaryFraction.Operation) (a b : BinaryFraction × ℕ) : BinaryFraction × ℕ :=
  let q := op.countedEval a.1 b.1
  (q.1,a.2+b.2+q.2)

def countedBinaryEval (x : ι → BinaryFraction) : ArithmeticExpression ι → BinaryFraction × ℕ
  | .integer z => let q := BinaryFraction.ofInt z; (q,2*q.width+2)
  | .input i => let q := x i; (q,2*q.width+2)
  | .add a b => countedBinaryNode .add (countedBinaryEval x a) (countedBinaryEval x b)
  | .sub a b => countedBinaryNode .sub (countedBinaryEval x a) (countedBinaryEval x b)
  | .mul a b => countedBinaryNode .mul (countedBinaryEval x a) (countedBinaryEval x b)
  | .div a b => countedBinaryNode .div (countedBinaryEval x a) (countedBinaryEval x b)
  | .minimum a b => countedBinaryNode .minimum (countedBinaryEval x a) (countedBinaryEval x b)
  | .maximum a b => countedBinaryNode .maximum (countedBinaryEval x a) (countedBinaryEval x b)

lemma countedBinaryEval_semantics (x : ι → BinaryFraction)
    (hx : ∀ i, 0 < binaryWordValue (x i).denominator) (e : ArithmeticExpression ι) :
    let q := countedBinaryEval x e
    q.1.value = eval (fun i => (x i).value) e ∧ 0 < binaryWordValue q.1.denominator := by
  induction e with
  | integer z => exact ⟨BinaryFraction.ofInt_value z,(show 0 < binaryWordValue [true] by decide)⟩
  | input i => exact ⟨rfl,hx i⟩
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib | minimum a b ia ib | maximum a b ia ib =>
    let u := (countedBinaryEval x a).1
    let v := (countedBinaryEval x b).1
    have h (op : BinaryFraction.Operation) : (op.countedEval u v).1.value =
          op.eval (eval (fun i => (x i).value) a) (eval (fun i => (x i).value) b) ∧
        0 < binaryWordValue (op.countedEval u v).1.denominator := by
      have hc := op.countedEval_correct u v ia.2 ib.2
      exact ⟨hc.1.trans (congrArg₂ op.eval ia.1 ib.1),hc.2⟩
    exact h _

private lemma countedBinaryNode_correct (x : ι → BinaryFraction) (op : BinaryFraction.Operation)
    (a b : ArithmeticExpression ι) (B W : ℕ) (hW : 1 ≤ W) (hw : W = (B+1)*(a.work+b.work+1)+1)
    (ha : (countedBinaryEval x a).1.value = eval (fun i => (x i).value) a ∧
      0 < binaryWordValue (countedBinaryEval x a).1.denominator ∧
      (countedBinaryEval x a).1.width ≤ (B+1)*a.work+1 ∧
      (countedBinaryEval x a).2 ≤ a.work*(3500*((B+1)*a.work+2)^3))
    (hb : (countedBinaryEval x b).1.value = eval (fun i => (x i).value) b ∧
      0 < binaryWordValue (countedBinaryEval x b).1.denominator ∧
      (countedBinaryEval x b).1.width ≤ (B+1)*b.work+1 ∧
      (countedBinaryEval x b).2 ≤ b.work*(3500*((B+1)*b.work+2)^3))
    (hH : RationalHeight (op.eval (eval (fun i => (x i).value) a) (eval (fun i => (x i).value) b)) (W-1)) :
    let q := countedBinaryNode op (countedBinaryEval x a) (countedBinaryEval x b)
    q.1.value = op.eval (eval (fun i => (x i).value) a) (eval (fun i => (x i).value) b) ∧
      0 < binaryWordValue q.1.denominator ∧ q.1.width ≤ W ∧
      q.2 ≤ (a.work+b.work+1)*(3500*(W+1)^3) := by
  let u := countedBinaryEval x a
  let v := countedBinaryEval x b
  have h := op.countedEval_correct u.1 v.1 ha.2.1 hb.2.1
  have huW : (B+1)*a.work+1 ≤ W := by rw [hw,Nat.mul_add,Nat.mul_add]; omega
  have hvW : (B+1)*b.work+1 ≤ W := by rw [hw,Nat.mul_add,Nat.mul_add]; omega
  have hu : u.1.width ≤ W := ha.2.2.1.trans huW
  have hv : v.1.width ≤ W := hb.2.2.1.trans hvW
  have hop := op.countedEval_work u.1 v.1 ha.2.1 hb.2.1 W hW hu hv
  refine ⟨h.1.trans (congrArg₂ op.eval ha.1 hb.1),h.2,?_,?_⟩
  · have hA : RationalHeight (op.eval u.1.value v.1.value) (W-1) := by rwa [ha.1,hb.1]
    have hWidth := op.countedEval_width u.1 v.1 ha.2.1 hb.2.1 (W-1)
      (by rw [Nat.sub_add_cancel hW]; exact hu) (by rw [Nat.sub_add_cancel hW]; exact hv) hA
    rwa [Nat.sub_add_cancel hW] at hWidth
  · let C := 3500*(W+1)^3
    have hU : u.2 ≤ a.work*C := ha.2.2.2.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 3)))
    have hV : v.2 ≤ b.work*C := hb.2.2.2.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 3)))
    exact (Nat.add_le_add (Nat.add_le_add hU hV) hop).trans_eq (by ring)

/-- Exact evaluation and a hard bit-step bound for the actual binary
expression evaluator. -/
theorem countedBinaryEval_correct (x : ι → BinaryFraction) (B : ℕ)
    (hx : ∀ i, 0 < binaryWordValue (x i).denominator ∧ (x i).width ≤ B+1 ∧ RationalHeight (x i).value B)
    (e : ArithmeticExpression ι) (he : LiteralsBounded B e) :
    let q := countedBinaryEval x e
    q.1.value = eval (fun i => (x i).value) e ∧ 0 < binaryWordValue q.1.denominator ∧
      q.1.width ≤ (B+1)*e.work+1 ∧ q.2 ≤ e.work*(3500*((B+1)*e.work+2)^3) := by
  induction e with
  | integer z =>
    have hz := BinaryFraction.ofInt_width z B he
    refine ⟨BinaryFraction.ofInt_value z,(show 0 < binaryWordValue [true] by decide),hz.trans (by simp [work]),?_⟩
    change 2*(BinaryFraction.ofInt z).width+2 ≤ 1*(3500*((B+1)*1+2)^3)
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]
  | input i =>
    refine ⟨rfl,(hx i).1,(hx i).2.1.trans (by simp [work]),?_⟩
    change 2*(x i).width+2 ≤ 1*(3500*((B+1)*1+2)^3)
    nlinarith [(hx i).2.1,Nat.zero_le (B^2),Nat.zero_le (B^3)]
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib | minimum a b ia ib | maximum a b ia ib =>
    have hA := ia he.1
    have hB := ib he.2
    let W := (B+1)*(a.work+b.work+1)+1
    have hW : 1 ≤ W := by dsimp [W]; omega
    have h := eval_rationalHeight (fun i => (x i).value) B (fun i => (hx i).2.2) _ he
    have hw : W-1 = (B+1)*(a.work+b.work+1) := rfl
    simp only [work] at h
    rw [← hw] at h
    exact countedBinaryNode_correct x _ a b B W hW rfl hA hB h

end ArithmeticExpression

end ProphetSecretary.Analysis
