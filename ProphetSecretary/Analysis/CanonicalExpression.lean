import ProphetSecretary.Analysis.BinaryRationalWork
import ProphetSecretary.Analysis.ArithmeticExpressionMap

/-!
# Counted expressions with canonical binary results

Each arithmetic node returns a canonical word immediately. Its cost is
bounded from the mathematical operand height, without a separate pass
over the finished expression.
-/

namespace ProphetSecretary.Analysis.ArithmeticExpression

variable {ι : Type*}

private def canonicalNode (op : BinaryFraction.Operation) (a b : BinaryRational × ℕ) : BinaryRational × ℕ :=
  let q := BinaryRational.countedOperation op a.1 b.1
  (q.1,a.2+b.2+q.2)

def countedCanonicalEval (x : ι → BinaryRational) : ArithmeticExpression ι → BinaryRational × ℕ
  | .integer z => let q : BinaryRational := z; (q,2*q.storage.width+2)
  | .input i => let q := x i; (q,2*q.storage.width+2)
  | .add a b => canonicalNode .add (countedCanonicalEval x a) (countedCanonicalEval x b)
  | .sub a b => canonicalNode .sub (countedCanonicalEval x a) (countedCanonicalEval x b)
  | .mul a b => canonicalNode .mul (countedCanonicalEval x a) (countedCanonicalEval x b)
  | .div a b => canonicalNode .div (countedCanonicalEval x a) (countedCanonicalEval x b)
  | .minimum a b => canonicalNode .minimum (countedCanonicalEval x a) (countedCanonicalEval x b)
  | .maximum a b => canonicalNode .maximum (countedCanonicalEval x a) (countedCanonicalEval x b)

lemma countedCanonicalEval_value (x : ι → BinaryRational) (e : ArithmeticExpression ι) :
    (countedCanonicalEval x e).1=eval x e := by
  induction e with
  | integer z => rfl
  | input i => rfl
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib | minimum a b ia ib | maximum a b ia ib =>
    simp only [countedCanonicalEval,canonicalNode,BinaryRational.countedOperation_value,
      BinaryRational.applyOperation,eval,ia,ib]

lemma canonicalEval_project (x : ι → BinaryRational) (e : ArithmeticExpression ι) :
    (countedCanonicalEval x e).1.value=eval (fun i => (x i).value) e := by
  rw [countedCanonicalEval_value]
  exact eval_map_value BinaryRational.valueHom BinaryRational.value_strictMono x e

private lemma canonicalNode_work (op : BinaryFraction.Operation) (a b : BinaryRational × ℕ)
    (B W₁ W₂ : ℕ)
    (hA : RationalHeight a.1.value ((B+1)*W₁)) (hB : RationalHeight b.1.value ((B+1)*W₂))
    (ha : a.2≤W₁*(3600*((B+1)*W₁+2)^3)) (hb : b.2≤W₂*(3600*((B+1)*W₂+2)^3)) :
    (canonicalNode op a b).2≤(W₁+W₂+1)*(3600*((B+1)*(W₁+W₂+1)+2)^3) := by
  let U := (B+1)*(W₁+W₂+1)
  let C := 3600*(U+2)^3
  have h₁ : (B+1)*W₁≤U := Nat.mul_le_mul_left _ (by omega)
  have h₂ : (B+1)*W₂≤U := Nat.mul_le_mul_left _ (by omega)
  have hO : (BinaryRational.countedOperation op a.1 b.1).2≤C :=
    BinaryRational.countedOperation_work op a.1 b.1 U (hA.mono h₁) (hB.mono h₂)
  have ha' : a.2≤W₁*C := ha.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 2) 3)))
  have hb' : b.2≤W₂*C := hb.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right h₂ 2) 3)))
  exact (Nat.add_le_add (Nat.add_le_add ha' hb') hO).trans_eq (by ring)

theorem countedCanonicalEval_work (x : ι → BinaryRational) (B : ℕ)
    (hx : ∀ i, RationalHeight (x i).value B) (e : ArithmeticExpression ι) (he : LiteralsBounded B e) :
    (countedCanonicalEval x e).2≤e.work*(3600*((B+1)*e.work+2)^3) := by
  induction e with
  | integer z =>
    have hz : RationalHeight (z:BinaryRational).value B := by
      rw [show (z:BinaryRational).value=(z:ℚ) from BinaryRational.ofRat_value z]
      exact rationalHeight_intCast z B he
    have hw := BinaryRational.storage_width z B hz
    change 2*(z:BinaryRational).storage.width+2≤1*(3600*((B+1)*1+2)^3)
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]
  | input i =>
    have hw := BinaryRational.storage_width (x i) B (hx i)
    change 2*(x i).storage.width+2≤1*(3600*((B+1)*1+2)^3)
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib | minimum a b ia ib | maximum a b ia ib =>
    have hA : RationalHeight (countedCanonicalEval x a).1.value ((B+1)*a.work) := by
      rw [canonicalEval_project]
      exact eval_rationalHeight _ B hx a he.1
    have hB : RationalHeight (countedCanonicalEval x b).1.value ((B+1)*b.work) := by
      rw [canonicalEval_project]
      exact eval_rationalHeight _ B hx b he.2
    exact canonicalNode_work _ _ _ B a.work b.work hA hB (ia he.1) (ib he.2)

lemma countedCanonicalEval_work_le (x : ι → BinaryRational) (B W : ℕ)
    (hx : ∀ i, RationalHeight (x i).value B) (e : ArithmeticExpression ι) (he : LiteralsBounded B e)
    (hw : e.work≤W) : (countedCanonicalEval x e).2≤W*(3600*((B+1)*W+2)^3) := by
  have h := Nat.add_le_add_right (Nat.mul_le_mul_left (B+1) hw) 2
  exact (countedCanonicalEval_work x B hx e he).trans
    (Nat.mul_le_mul hw (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)))

end ProphetSecretary.Analysis.ArithmeticExpression
