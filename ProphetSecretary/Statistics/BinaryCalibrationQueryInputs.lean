import ProphetSecretary.Statistics.BinaryCalibrationPublic
import ProphetSecretary.Statistics.FairCalibratedNativeCalls

/-!
# Binary calculation of the public query inputs

The target and threshold tolerances, their failure probabilities and the
common bound on the planner weight are calculated by exact encoded
arithmetic. These calculations are independent of all observed samples.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis
open FairCalibrationParameters

namespace CalibrationBinaryExpr

def repeatedProduct (x : CalibrationBinaryExpr) : ℕ → CalibrationBinaryExpr
  | 0 => .atom 1
  | k+1 => .node .mul (repeatedProduct x k) x

@[simp] lemma repeatedProduct_value (x : CalibrationBinaryExpr) (k : ℕ) :
    (repeatedProduct x k).value=x.value^k := by
  induction k with
  | zero => simp [repeatedProduct,value,BinaryRational.one_value]
  | succ k ih => simp only [repeatedProduct,value,rationalCalibrationOp,ih,pow_succ]

lemma repeatedProduct_size (x : CalibrationBinaryExpr) (k : ℕ) :
    (repeatedProduct x k).size=1+k*(x.size+1) := by
  induction k with
  | zero => simp [repeatedProduct,size]
  | succ k ih => simp only [repeatedProduct,size,ih,Nat.succ_mul]; omega

lemma repeatedProduct_leaves (x : CalibrationBinaryExpr) (k B : ℕ) (h : x.leavesFit B) :
    (repeatedProduct x k).leavesFit B := by
  induction k with
  | zero =>
    simp only [repeatedProduct,leavesFit,BinaryRational.one_value]
    exact rationalHeight_one.mono (Nat.zero_le _)
  | succ k ih => exact ⟨ih,h⟩

end CalibrationBinaryExpr

open CalibrationBinaryExpr

def binaryQueryInputExpr (n m J count zlo : BinaryRational) (i : Fin 5) : CalibrationBinaryExpr :=
  let x := CalibrationBinaryExpr.atom m
  let t := CalibrationBinaryExpr.atom (BinaryRational.ofRat 2)
  let f := CalibrationBinaryExpr.atom (BinaryRational.ofRat 4)
  let u := CalibrationBinaryExpr.atom 1
  let mm : CalibrationBinaryExpr := .node .mul x x
  let cl : CalibrationBinaryExpr := .node .add u (.atom count)
  match i.val with
  | 0 => .node .mul (.atom (BinaryRational.ofRat ((4 : ℚ)^8))) (repeatedProduct (.node .mul t x) 32)
  | 1 => .node .div u x
  | 2 => .node .div u (.node .mul mm (.node .add (.node .mul f x) u))
  | 3 => .node .div (.node .div (.atom zlo) (.node .mul x (.node .mul cl cl))) t
  | _ => .node .div u (.node .mul (.node .mul mm (.atom n)) (.node .add (.atom J) u))

def countedBinaryCalibrationQueryInputs (n m J : ℕ) (zlo : BinaryRational) :
    (Fin 5 → BinaryRational) × ℕ :=
  let N := countedCalibrationNat n
  let M := countedCalibrationNat m
  let K := countedCalibrationNat J
  let R := countedCalibrationNat (4*(m-1).bits.length+2)
  let q := Vector.ofFn fun i => (binaryQueryInputExpr N.1 M.1 K.1 R.1 zlo i).evaluate
  (fun i => (q.get i).1,N.2+M.2+K.2+R.2+4*(m-1).bits.length+
    (∑ i : Fin 5, ((q.get i).2+2))+10)

private lemma vector_get_ofFn {A : Type*} {N : ℕ} (f : Fin N → A) (i : Fin N) :
    (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt

theorem countedBinaryCalibrationQueryInputs_value (n m J : ℕ) (zlo : BinaryRational) :
    let x := (countedBinaryCalibrationQueryInputs n m J zlo).1
    (x 0).value=rationalCalibrationWeightBound m ∧
      (x 1).value=rationalTargetTolerance m ∧
      (x 2).value=rationalTargetFailure m ∧
      (x 3).value=rationalThresholdTolerance m zlo.value ∧
      (x 4).value=rationalThresholdFailure n m J := by
  norm_num [countedBinaryCalibrationQueryInputs,vector_get_ofFn,evaluate_value,binaryQueryInputExpr,
    value,rationalCalibrationOp,←calibrationClog_eq_width,rationalCalibrationWeightBound,
    rationalTargetTolerance,rationalTargetFailure,rationalThresholdTolerance,rationalThresholdFailure,pow_two]

private lemma binaryQueryInputExpr_size (n m J count zlo : BinaryRational) (i : Fin 5) :
    (binaryQueryInputExpr n m J count zlo i).size≤150 := by
  fin_cases i <;> norm_num [binaryQueryInputExpr,size,repeatedProduct_size]

private lemma binaryQueryInputExpr_leaves (n m J count zlo : BinaryRational) (i : Fin 5) (B : ℕ)
    (hB : 16≤B) (hn : RationalHeight n.value B) (hm : RationalHeight m.value B)
    (hJ : RationalHeight J.value B) (hC : RationalHeight count.value B)
    (hz : RationalHeight zlo.value B) :
    (binaryQueryInputExpr n m J count zlo i).leavesFit B := by
  have h1 : RationalHeight (1 : ℚ) B := rationalHeight_one.mono (by omega)
  have h2 : RationalHeight (2 : ℚ) B := (rationalHeight_natCast 2 1 (by decide)).mono (by omega)
  have h4 : RationalHeight (4 : ℚ) B := (rationalHeight_natCast 4 2 (by decide)).mono (by omega)
  have hβ : RationalHeight ((4 : ℚ)^8) B := ((rationalHeight_natCast 4 2 (by decide)).pow 8).mono hB
  have hpow : (repeatedProduct (.node .mul (.atom (BinaryRational.ofRat 2)) (.atom m)) 32).leavesFit B :=
    repeatedProduct_leaves _ _ _ (by simpa only [leavesFit,BinaryRational.ofRat_value] using ⟨h2,hm⟩)
  fin_cases i <;> simp [binaryQueryInputExpr,leavesFit,h1,h2,h4,hβ,hn,hm,hJ,hC,hz,hpow]

def binaryCalibrationQueryInputsWork (m B : ℕ) : ℕ :=
  4*(3*(B+1)+3)+4*m+5*(150*CalibrationBinaryExpr.workUnit 150 B+2)+10

theorem countedBinaryCalibrationQueryInputs_bounds (n m J : ℕ) (zlo : BinaryRational) (B : ℕ)
    (hB : 16≤B) (hn : n≤2^B) (hm : m≤2^B) (hJ : J≤2^B)
    (hR : 4*(m-1).bits.length+2≤2^B) (hz : RationalHeight zlo.value B) :
    let q := countedBinaryCalibrationQueryInputs n m J zlo
    (∀ i, RationalHeight (q.1 i).value (150*(B+1))) ∧ q.2≤binaryCalibrationQueryInputsWork m B := by
  dsimp only
  let N := countedCalibrationNat n
  let M := countedCalibrationNat m
  let K := countedCalibrationNat J
  let R := countedCalibrationNat (4*(m-1).bits.length+2)
  let e := binaryQueryInputExpr N.1 M.1 K.1 R.1 zlo
  have hFit (i : Fin 5) : (e i).leavesFit B :=
    binaryQueryInputExpr_leaves _ _ _ _ _ i B hB
      (by rw [countedCalibrationNat_value]; exact rationalHeight_natCast _ _ hn)
      (by rw [countedCalibrationNat_value]; exact rationalHeight_natCast _ _ hm)
      (by rw [countedCalibrationNat_value]; exact rationalHeight_natCast _ _ hJ)
      (by rw [countedCalibrationNat_value]; exact rationalHeight_natCast _ _ hR) hz
  constructor
  · intro i
    simp only [countedBinaryCalibrationQueryInputs,vector_get_ofFn,evaluate_value]
    exact ((e i).value_height B (hFit i)).mono (Nat.mul_le_mul_right _ (binaryQueryInputExpr_size _ _ _ _ _ i))
  · simp only [countedBinaryCalibrationQueryInputs,vector_get_ofFn,binaryCalibrationQueryInputsWork]
    have h1 := countedCalibrationNat_work n B hn
    have h2 := countedCalibrationNat_work m B hm
    have h3 := countedCalibrationNat_work J B hJ
    have h4 := countedCalibrationNat_work (4*(m-1).bits.length+2) B hR
    have hl := clog_two_le_self m
    rw [calibrationClog_eq_width] at hl
    have hSum : (∑ i : Fin 5, ((e i).evaluate.2+2))≤5*(150*workUnit 150 B+2) := by
      calc
        _ ≤ ∑ _i : Fin 5, (150*workUnit 150 B+2) := by
          apply Finset.sum_le_sum
          intro i _
          have hs := binaryQueryInputExpr_size N.1 M.1 K.1 R.1 zlo i
          exact Nat.add_le_add_right (((e i).evaluate_work 150 B (hFit i) hs).trans
            (Nat.mul_le_mul_right _ hs)) _
        _ = _ := by simp
    change N.2+M.2+K.2+R.2+4*(m-1).bits.length+(∑ i : Fin 5, ((e i).evaluate.2+2))+10≤_
    dsimp only [N,M,K,R,e] at hSum ⊢
    omega

end ProphetSecretary.Statistics.Calibration
