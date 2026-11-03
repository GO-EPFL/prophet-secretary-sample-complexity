import ProphetSecretary.Analysis.ArithmeticExpression
import ProphetSecretary.Analysis.RationalHeight

/-!
# Rational sizes of arithmetic expressions

An arithmetic expression is a tree. With bounded inputs and integer
literals, every intermediate value has height at most the number of nodes
times the common input bound plus one.
-/

namespace ProphetSecretary.Analysis.ArithmeticExpression

variable {ι : Type*}

def LiteralsBounded (B : ℕ) : ArithmeticExpression ι → Prop
  | .integer z => z.natAbs ≤ 2^B
  | .input _ => True
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b =>
    LiteralsBounded B a ∧ LiteralsBounded B b

lemma LiteralsBounded.mono {B C : ℕ} {e : ArithmeticExpression ι} (h : LiteralsBounded B e) (hBC : B ≤ C) :
    LiteralsBounded C e := by
  induction e with
  | integer z => exact h.trans (Nat.pow_le_pow_right (by decide) hBC)
  | input i => trivial
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib | minimum a b ia ib | maximum a b ia ib =>
    exact ⟨ia h.1,ib h.2⟩

lemma literalsBounded_sumList {α : Type*} (l : List α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ l, LiteralsBounded B (f i)) : LiteralsBounded B (sumList l f) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih => exact ⟨h i List.mem_cons_self,ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

lemma literalsBounded_productList {α : Type*} (l : List α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ l, LiteralsBounded B (f i)) : LiteralsBounded B (productList l f) := by
  induction l with
  | nil => exact Nat.succ_le_of_lt (by positivity)
  | cons i l ih => exact ⟨h i List.mem_cons_self,ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

lemma literalsBounded_maximumList {α : Type*} (l : List α) (f : α → ArithmeticExpression ι)
    (B : ℕ) (h : ∀ i ∈ l, LiteralsBounded B (f i)) : LiteralsBounded B (maximumList l f) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih => exact ⟨h i List.mem_cons_self,ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

lemma eval_rationalHeight (x : ι → ℚ) (B : ℕ) (hx : ∀ i, RationalHeight (x i) B)
    (e : ArithmeticExpression ι) (he : LiteralsBounded B e) :
    RationalHeight (eval x e) ((B+1)*e.work) := by
  induction e with
  | integer z => exact (rationalHeight_intCast z B he).mono (by simp [work])
  | input i => exact (hx i).mono (by simp [work])
  | add a b ia ib =>
    apply ((ia he.1).add (ib he.2)).mono
    simp only [work,Nat.mul_add,Nat.mul_one]
    omega
  | sub a b ia ib =>
    apply ((ia he.1).sub (ib he.2)).mono
    simp only [work,Nat.mul_add,Nat.mul_one]
    omega
  | mul a b ia ib =>
    apply ((ia he.1).mul (ib he.2)).mono
    simp only [work,Nat.mul_add,Nat.mul_one]
    omega
  | div a b ia ib =>
    apply ((ia he.1).div (ib he.2)).mono
    simp only [work,Nat.mul_add,Nat.mul_one]
    omega
  | minimum a b ia ib =>
    apply ((ia he.1).min (ib he.2)).mono
    apply max_le <;> simp only [work,Nat.mul_add,Nat.mul_one] <;> omega
  | maximum a b ia ib =>
    apply ((ia he.1).max (ib he.2)).mono
    apply max_le <;> simp only [work,Nat.mul_add,Nat.mul_one] <;> omega

/-- The intermediate arithmetic values of one expression, including its
inputs and output. This list is used to state the uniform height bound. -/
def evalValues (x : ι → ℚ) : ArithmeticExpression ι → List ℚ
  | .integer z => [z]
  | .input i => [x i]
  | .add a b => (eval x a + eval x b) :: (evalValues x a ++ evalValues x b)
  | .sub a b => (eval x a - eval x b) :: (evalValues x a ++ evalValues x b)
  | .mul a b => (eval x a * eval x b) :: (evalValues x a ++ evalValues x b)
  | .div a b => (eval x a / eval x b) :: (evalValues x a ++ evalValues x b)
  | .minimum a b => min (eval x a) (eval x b) :: (evalValues x a ++ evalValues x b)
  | .maximum a b => max (eval x a) (eval x b) :: (evalValues x a ++ evalValues x b)

lemma evalValues_rationalHeight (x : ι → ℚ) (B : ℕ) (hx : ∀ i, RationalHeight (x i) B)
    (e : ArithmeticExpression ι) (he : LiteralsBounded B e) (q : ℚ) (hq : q ∈ e.evalValues x) :
    RationalHeight q ((B+1)*e.work) := by
  induction e with
  | integer z =>
    have hh : q = z := List.mem_singleton.mp hq
    rw [hh]
    exact eval_rationalHeight x B hx _ he
  | input i =>
    have hh : q = x i := List.mem_singleton.mp hq
    rw [hh]
    exact eval_rationalHeight x B hx _ he
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib | minimum a b ia ib | maximum a b ia ib =>
    simp only [evalValues,List.mem_cons,List.mem_append] at hq
    rcases hq with heq | hqa | hqb
    · rw [heq]
      exact eval_rationalHeight x B hx _ he
    · exact (ia he.1 hqa).mono (Nat.mul_le_mul_left _ (by simp only [work]; omega))
    · exact (ib he.2 hqb).mono (Nat.mul_le_mul_left _ (by simp only [work]; omega))

end ProphetSecretary.Analysis.ArithmeticExpression
