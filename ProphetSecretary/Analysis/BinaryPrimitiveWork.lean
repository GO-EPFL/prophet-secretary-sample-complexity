import ProphetSecretary.Analysis.ArithmeticExpressionBits
import ProphetSecretary.Analysis.BinaryRationalFloor

/-!
# Work of a finite binary arithmetic trace

Each numeric instruction is evaluated by the counted binary algorithm.
The uniform charge bounds these actual counters; it is not a replacement
for the arithmetic semantics or a definition of the executed work.
-/

namespace ProphetSecretary.Analysis

inductive BinaryPrimitive where
  | arithmetic (op : BinaryFraction.Operation) (x y : BinaryFraction)
  | comparison (x y : BinaryFraction)
  | nonnegativeFloor (x : ℚ)
  | word (width : ℕ)

def BinaryPrimitive.work : BinaryPrimitive → ℕ
  | .arithmetic op x y => (op.countedEval x y).2
  | .comparison x y => (x.countedLE y).2
  | .nonnegativeFloor x => (countedRationalFloorBits x).2
  | .word w => 4*(w+1)

def BinaryPrimitive.Fits (B : ℕ) : BinaryPrimitive → Prop
  | .arithmetic _ x y | .comparison x y =>
    0 < binaryWordValue x.denominator ∧ 0 < binaryWordValue y.denominator ∧
      x.width≤B+1 ∧ y.width≤B+1
  | .nonnegativeFloor x => RationalHeight x B
  | .word w => w≤B+1

def binaryPrimitiveCharge (B : ℕ) : ℕ := 3500*(B+2)^3

theorem BinaryPrimitive.work_le (B : ℕ) (q : BinaryPrimitive) (h : q.Fits B) :
    q.work ≤ binaryPrimitiveCharge B := by
  cases q with
  | arithmetic op x y =>
    exact BinaryFraction.Operation.countedEval_work op x y h.1 h.2.1 (B+1) (by omega) h.2.2.1 h.2.2.2
  | comparison x y =>
    exact (BinaryFraction.countedLE_work x y (B+1) h.2.2.1 h.2.2.2 h.1 h.2.1).trans
      (Nat.mul_le_mul_right _ (by decide))
  | nonnegativeFloor x =>
    refine (countedRationalFloorBits_work x B h).trans ?_
    unfold binaryPrimitiveCharge
    exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by positivity) (by decide))
  | word w =>
    change w≤B+1 at h
    change 4*(w+1)≤3500*(B+2)^3
    have hP : B+2 ≤ (B+2)^3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by positivity : 0<B+2) (by decide : (1:ℕ)≤3)
    exact Nat.mul_le_mul (by decide) ((Nat.add_le_add_right h 1).trans hP)

def binaryPrimitiveTraceWork (q : List BinaryPrimitive) : ℕ := (q.map BinaryPrimitive.work).sum

theorem binaryPrimitiveTraceWork_le (q : List BinaryPrimitive) (B : ℕ)
    (h : ∀ p ∈ q, p.Fits B) : binaryPrimitiveTraceWork q ≤ q.length*binaryPrimitiveCharge B := by
  induction q with
  | nil => simp [binaryPrimitiveTraceWork]
  | cons p q ih =>
    have hp := p.work_le B (h p List.mem_cons_self)
    have hq := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    change p.work+binaryPrimitiveTraceWork q ≤ (q.length+1)*binaryPrimitiveCharge B
    rw [Nat.add_mul,Nat.one_mul]
    omega

end ProphetSecretary.Analysis
