import ProphetSecretary.Statistics.BinaryPlannerSampler
import ProphetSecretary.Statistics.ScalarPlannerValueMap
import ProphetSecretary.Statistics.PlannerPrimitiveHeight

/-!
# Active identities and weight products on binary words

The active scan compares each stored probability with zero. The product
uses three binary arithmetic calls per retained identity.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ}

def binaryPositiveTest (x : BinaryRational) : Bool × ℕ :=
  let q := x.storage.countedLE (BinaryRational.ofRat 0).storage
  (!q.1,q.2+2)

lemma binaryPositiveTest_value (x : BinaryRational) : (binaryPositiveTest x).1 = decide (0<x) := by
  have h := BinaryFraction.countedLE_correct x.storage (BinaryRational.ofRat 0).storage
    (BinaryRational.storage_denominator_pos x) (BinaryRational.storage_denominator_pos _)
  have he : (x.storage.countedLE (BinaryRational.ofRat 0).storage).1=true ↔ x.value≤0 := by
    change (x.storage.countedLE (BinaryRational.ofRat 0).storage).1=true ↔ x.storage.value≤0
    simpa only [show (BinaryRational.ofRat 0).storage.value=(0:ℚ) from BinaryRational.ofRat_value 0] using h
  apply Bool.eq_iff_iff.mpr
  simp only [binaryPositiveTest,Bool.not_eq_true',decide_eq_true_eq]
  change (x.storage.countedLE (BinaryRational.ofRat 0).storage).1=false ↔ (0:BinaryRational).value<x.value
  rw [BinaryRational.zero_value,Bool.eq_false_iff]
  exact (not_congr he).trans not_le

def countedBinaryPlannerActive (p : Fin n → BinaryRational) (l : List (Fin n)) : List (Fin n) × ℕ :=
  countedBinaryFilter (fun i => binaryPositiveTest (p i)) l

lemma countedBinaryPlannerActive_value (p : Fin n → BinaryRational) (l : List (Fin n)) :
    (countedBinaryPlannerActive p l).1 = (countedPlannerActive p l).1 := by
  simp only [countedBinaryPlannerActive,countedBinaryFilter_value,binaryPositiveTest_value,countedPlannerActive_value]

lemma countedBinaryPlannerActive_work (p : Fin n → BinaryRational) (l : List (Fin n)) (B : ℕ)
    (hP : ∀ i, RationalHeight (p i).value B) :
    (countedBinaryPlannerActive p l).2≤1+l.length*(3400*(B+2)^3+5) := by
  have hTest (i : Fin n) : (binaryPositiveTest (p i)).2≤3400*(B+2)^3+2 := by
    change ((p i).storage.countedLE (BinaryRational.ofRat 0).storage).2+2≤_
    apply Nat.add_le_add_right
    exact BinaryFraction.countedLE_work _ _ (B+1) (BinaryRational.storage_width _ B (hP i))
      (BinaryRational.storage_width _ B (by rw [BinaryRational.ofRat_value]; exact rationalHeight_zero.mono (Nat.zero_le _)))
      (BinaryRational.storage_denominator_pos _) (BinaryRational.storage_denominator_pos _)
  exact (countedBinaryFilter_work _ l _ (fun i _ => hTest i)).trans_eq (by ring)

def countedBinaryPlannerWeight (p : Fin n → BinaryRational) : List (Fin n) → BinaryRational × ℕ
  | [] => (1,1)
  | i::l =>
    let q := countedBinaryPlannerWeight p l
    let a := BinaryRational.countedOperation .mul 4 (p i)
    let b := BinaryRational.countedOperation .add 1 a.1
    let w := BinaryRational.countedOperation .mul b.1 q.1
    (w.1,q.2+a.2+b.2+w.2+5)

lemma countedBinaryPlannerWeight_value (p : Fin n → BinaryRational) (l : List (Fin n)) :
    (countedBinaryPlannerWeight p l).1=(countedPlannerWeight p l).1 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [countedBinaryPlannerWeight,countedPlannerWeight,BinaryRational.countedOperation_value,
      BinaryRational.applyOperation,ih]

lemma countedBinaryPlannerWeight_height (p : Fin n → BinaryRational) (l : List (Fin n)) (P : ℕ)
    (hp : ∀ i, RationalHeight (p i).value P) :
    RationalHeight (countedBinaryPlannerWeight p l).1.value (l.length*(P+3)) := by
  rw [countedBinaryPlannerWeight_value]
  change RationalHeight (BinaryRational.valueHom (countedPlannerWeight p l).1) _
  rw [← countedPlannerWeight_valueMap BinaryRational.valueHom]
  exact countedPlannerWeight_height (fun i => (p i).value) P hp l

theorem countedBinaryPlannerWeight_work (p : Fin n → BinaryRational) (l : List (Fin n)) (P M : ℕ)
    (hp : ∀ i, RationalHeight (p i).value P) (hL : l.length≤M) :
    let B := M*(P+3)+P+3
    (countedBinaryPlannerWeight p l).2≤1+l.length*(3*(3600*(B+2)^3)+5) := by
  let B := M*(P+3)+P+3
  let C := 3600*(B+2)^3
  change (countedBinaryPlannerWeight p l).2≤1+l.length*(3*C+5)
  induction l with
  | nil => simp [countedBinaryPlannerWeight]
  | cons i l ih =>
    let q := countedBinaryPlannerWeight p l
    let a := BinaryRational.countedOperation .mul 4 (p i)
    let b := BinaryRational.countedOperation .add 1 a.1
    let w := BinaryRational.countedOperation .mul b.1 q.1
    have hM : l.length≤M := (Nat.le_succ _).trans hL
    have hQ : q.2≤1+l.length*(3*C+5) := ih hM
    have hw : RationalHeight q.1.value B := (countedBinaryPlannerWeight_height p l P hp).mono (by
      have h := Nat.mul_le_mul_right (P+3) hM
      dsimp [B]
      omega)
    have h4 : RationalHeight (4:BinaryRational).value 2 := by
      rw [show (4:BinaryRational).value=(4:ℚ) from BinaryRational.ofRat_value 4]
      exact rationalHeight_four
    have h1 : RationalHeight (1:BinaryRational).value 0 := by rw [BinaryRational.one_value]; exact rationalHeight_one
    have ha : RationalHeight a.1.value (2+P) := by
      rw [BinaryRational.countedOperation_value]
      change RationalHeight (BinaryRational.mul 4 (p i)).value _
      rw [BinaryRational.mul_value]
      exact h4.mul (hp i)
    have hb : RationalHeight b.1.value (P+3) := by
      rw [BinaryRational.countedOperation_value]
      change RationalHeight (BinaryRational.add 1 a.1).value _
      rw [BinaryRational.add_value]
      exact (h1.add ha).mono (by omega)
    have hA : a.2≤C := BinaryRational.countedOperation_work .mul _ _ B
      (h4.mono (by dsimp [B]; omega)) ((hp i).mono (by dsimp [B]; omega))
    have hB : b.2≤C := BinaryRational.countedOperation_work .add _ _ B
      (h1.mono (Nat.zero_le _)) (ha.mono (by dsimp [B]; omega))
    have hW : w.2≤C := BinaryRational.countedOperation_work .mul _ _ B
      (hb.mono (by dsimp [B]; omega)) hw
    change q.2+a.2+b.2+w.2+5≤1+(l.length+1)*(3*C+5)
    rw [Nat.add_mul,Nat.one_mul]
    omega

end ProphetSecretary.Statistics
