import ProphetSecretary.Analysis.BinaryRationalWork

/-!
# Binary arithmetic in calibration

An arithmetic expression is evaluated by the actual counted binary
primitives. Its work follows from its own tree size and the widths of
its inputs. No list of intermediate operands is supplied to the bound.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

abbrev CalibrationBinary := BinaryRational

def countedCalibrationLE (x y : CalibrationBinary) : Bool × ℕ :=
  x.storage.countedLE y.storage

def countedCalibrationLT (x y : CalibrationBinary) : Bool × ℕ :=
  let q := countedCalibrationLE y x
  (!q.1,q.2+1)

def countedCalibrationEQ (x y : CalibrationBinary) : Bool × ℕ :=
  let p := countedCalibrationLE x y
  let q := countedCalibrationLE y x
  (p.1 && q.1,p.2+q.2+1)

@[simp] lemma countedCalibrationLE_value (x y : CalibrationBinary) :
    (countedCalibrationLE x y).1=decide (x.value≤y.value) := by
  apply Bool.eq_iff_iff.mpr
  exact (BinaryFraction.countedLE_correct _ _ (BinaryRational.storage_denominator_pos x)
    (BinaryRational.storage_denominator_pos y)).trans decide_eq_true_iff.symm

@[simp] lemma countedCalibrationLT_value (x y : CalibrationBinary) :
    (countedCalibrationLT x y).1=decide (x.value<y.value) := by
  by_cases h : x.value<y.value
  · have hn : ¬y.value≤x.value := not_le.mpr h
    simp [countedCalibrationLT,h,hn]
  · have hp : y.value≤x.value := le_of_not_gt h
    simp [countedCalibrationLT,h,hp]

@[simp] lemma countedCalibrationEQ_value (x y : CalibrationBinary) :
    (countedCalibrationEQ x y).1=decide (x.value=y.value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [countedCalibrationEQ,countedCalibrationLE_value,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨h.le,h.ge⟩⟩

def calibrationComparisonWork (B : ℕ) : ℕ := 6800*(B+2)^3+2

lemma countedCalibrationLE_work (x y : CalibrationBinary) (B : ℕ)
    (hx : RationalHeight x.value B) (hy : RationalHeight y.value B) :
    (countedCalibrationLE x y).2≤calibrationComparisonWork B := by
  have h := BinaryRational.countedOrderTest_work x y B hx hy
  unfold countedCalibrationLE calibrationComparisonWork
  omega

lemma countedCalibrationLT_work (x y : CalibrationBinary) (B : ℕ)
    (hx : RationalHeight x.value B) (hy : RationalHeight y.value B) :
    (countedCalibrationLT x y).2≤calibrationComparisonWork B := by
  have h := BinaryRational.countedOrderTest_work x y B hx hy
  unfold countedCalibrationLT countedCalibrationLE calibrationComparisonWork
  dsimp only
  omega

lemma countedCalibrationEQ_work (x y : CalibrationBinary) (B : ℕ)
    (hx : RationalHeight x.value B) (hy : RationalHeight y.value B) :
    (countedCalibrationEQ x y).2≤calibrationComparisonWork B := by
  have h := BinaryRational.countedOrderTest_work x y B hx hy
  unfold countedCalibrationEQ countedCalibrationLE calibrationComparisonWork
  dsimp only
  omega

def rationalCalibrationOp (op : BinaryFraction.Operation) (x y : ℚ) : ℚ :=
  match op with
  | .add => x+y
  | .sub => x-y
  | .mul => x*y
  | .div => x/y
  | .minimum => min x y
  | .maximum => max x y

@[simp] lemma countedCalibrationOp_value (op : BinaryFraction.Operation) (x y : CalibrationBinary) :
    (BinaryRational.countedOperation op x y).1.value=rationalCalibrationOp op x.value y.value := by
  rw [BinaryRational.countedOperation_value]
  cases op
  · exact BinaryRational.add_value _ _
  · exact BinaryRational.sub_value _ _
  · exact BinaryRational.mul_value _ _
  · exact BinaryRational.div_value _ _
  · exact BinaryRational.min_value _ _
  · exact BinaryRational.max_value _ _

lemma rationalCalibrationOp_height (op : BinaryFraction.Operation) {x y : ℚ} {A B : ℕ}
    (hx : RationalHeight x A) (hy : RationalHeight y B) :
    RationalHeight (rationalCalibrationOp op x y) (A+B+1) := by
  cases op
  · exact hx.add hy
  · exact hx.sub hy
  · exact (hx.mul hy).mono (by omega)
  · exact (hx.div hy).mono (by omega)
  · exact (hx.min hy).mono (max_le (by omega) (by omega))
  · exact (hx.max hy).mono (max_le (by omega) (by omega))

inductive CalibrationBinaryExpr
  | atom (x : CalibrationBinary)
  | node (op : BinaryFraction.Operation) (left right : CalibrationBinaryExpr)

namespace CalibrationBinaryExpr

def size : CalibrationBinaryExpr → ℕ
  | .atom _ => 1
  | .node _ a b => a.size+b.size+1

def leavesFit (B : ℕ) : CalibrationBinaryExpr → Prop
  | .atom x => RationalHeight x.value B
  | .node _ a b => a.leavesFit B ∧ b.leavesFit B

def evaluate : CalibrationBinaryExpr → CalibrationBinary × ℕ
  | .atom x => (x,1)
  | .node op a b =>
      let x := a.evaluate
      let y := b.evaluate
      let q := BinaryRational.countedOperation op x.1 y.1
      (q.1,x.2+y.2+q.2+1)

def value : CalibrationBinaryExpr → ℚ
  | .atom x => x.value
  | .node op a b => rationalCalibrationOp op a.value b.value

@[simp] lemma evaluate_value (e : CalibrationBinaryExpr) : e.evaluate.1.value=e.value := by
  induction e with
  | atom x => rfl
  | node op a b ia ib => simp only [evaluate,value,countedCalibrationOp_value,ia,ib]

theorem value_height (e : CalibrationBinaryExpr) (B : ℕ) (h : e.leavesFit B) :
    RationalHeight e.value (e.size*(B+1)) := by
  induction e with
  | atom x =>
    change RationalHeight x.value B at h
    exact h.mono (by simp [size])
  | node op a b ia ib =>
    change a.leavesFit B ∧ b.leavesFit B at h
    have hx := rationalCalibrationOp_height op (ia h.1) (ib h.2)
    apply hx.mono
    simp only [size,Nat.add_mul,Nat.one_mul]
    omega

def workUnit (L B : ℕ) : ℕ := 3600*(L*(B+1)+2)^3+1

/-- This bound is derived from the program tree and its input words. -/
theorem evaluate_work (e : CalibrationBinaryExpr) (L B : ℕ)
    (h : e.leavesFit B) (hL : e.size≤L) :
    e.evaluate.2≤e.size*workUnit L B := by
  induction e with
  | atom x =>
    change 1≤1*workUnit L B
    unfold workUnit
    omega
  | node op a b ia ib =>
    change a.leavesFit B ∧ b.leavesFit B at h
    have ha : a.size≤L := by simp only [size] at hL; omega
    have hb : b.size≤L := by simp only [size] at hL; omega
    have haW := ia h.1 ha
    have hbW := ib h.2 hb
    have haH : RationalHeight a.evaluate.1.value (L*(B+1)) := by
      rw [evaluate_value]
      exact (value_height a B h.1).mono (Nat.mul_le_mul_right _ ha)
    have hbH : RationalHeight b.evaluate.1.value (L*(B+1)) := by
      rw [evaluate_value]
      exact (value_height b B h.2).mono (Nat.mul_le_mul_right _ hb)
    have hop := BinaryRational.countedOperation_work op a.evaluate.1 b.evaluate.1 (L*(B+1)) haH hbH
    change a.evaluate.2+b.evaluate.2+(BinaryRational.countedOperation op a.evaluate.1 b.evaluate.1).2+1≤_
    simp only [size,Nat.add_mul,Nat.one_mul]
    unfold workUnit at *
    omega

end CalibrationBinaryExpr

end ProphetSecretary.Statistics.Calibration
