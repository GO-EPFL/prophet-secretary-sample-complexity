import ProphetSecretary.Statistics.BinaryPlannerWeights

/-!
# Computing the stored positive probabilities on binary words

The row scan counts positive observations. Its ratio is equal to the
complement of the closed empirical CDF at zero, with the same empty-row
convention as the scalar recursion.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

def countedBinaryRowProbability (l : List BinaryRational) : BinaryRational × ℕ :=
  let a := countedBinaryFilter binaryPositiveTest l
  let c := countedListLength a.1
  let d := countedListLength l
  let q := BinaryRational.countedOperation .div (c.1:BinaryRational) (d.1:BinaryRational)
  (q.1,a.2+c.2+d.2+q.2+10)

theorem countedBinaryRowProbability_value (l : List BinaryRational) :
    (countedBinaryRowProbability l).1=(countedPlannerRowProbability l).1 := by
  have he : (fun x : BinaryRational => decide (¬decide (x≤0)=true))=fun x => decide (0<x) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [not_le]
  have h := l.length_eq_countP_add_countP (fun x => decide (x≤0))
  rw [he] at h
  have hC := congrArg (fun n : ℕ => (n:BinaryRational)) h
  simp only [Nat.cast_add] at hC
  simp only [countedBinaryRowProbability,countedBinaryFilter_value,binaryPositiveTest_value,
    countedListLength_value,BinaryRational.countedOperation_value,BinaryRational.applyOperation,
    countedPlannerRowProbability,countedRowCDFCounts_value,← List.countP_eq_length_filter]
  congr 1
  rw [hC]
  ring

lemma countedBinaryRowProbability_height (l : List BinaryRational) (P : ℕ) (hP : l.length≤2^P) :
    RationalHeight (countedBinaryRowProbability l).1.value (2*P) := by
  rw [countedBinaryRowProbability_value]
  change RationalHeight (BinaryRational.valueHom (countedPlannerRowProbability l).1) _
  rw [← countedPlannerRowProbability_valueMap BinaryRational.valueHom BinaryRational.value_strictMono]
  exact countedPlannerRowProbability_height _ _ (by simpa only [List.length_map] using hP)

def binaryRowProbabilityWorkBound (m Y M : ℕ) : ℕ :=
  1+m*(3400*(Y+2)^3+5)+2*(1+2*m)+3600*(M+2)^3+10

theorem countedBinaryRowProbability_work (l : List BinaryRational) (m Y M : ℕ)
    (hl : l.length≤m) (hm : m≤2^M) (hY : ∀ x∈l, RationalHeight x.value Y) :
    (countedBinaryRowProbability l).2≤binaryRowProbabilityWorkBound m Y M := by
  let a := countedBinaryFilter binaryPositiveTest l
  let c := countedListLength a.1
  let d := countedListLength l
  let q := BinaryRational.countedOperation .div (c.1:BinaryRational) (d.1:BinaryRational)
  have hA : a.1.length≤l.length := by
    rw [countedBinaryFilter_value]
    exact List.length_filter_le _ _
  have hTest (x : BinaryRational) (hx : x∈l) : (binaryPositiveTest x).2≤3400*(Y+2)^3+2 := by
    change (x.storage.countedLE (BinaryRational.ofRat 0).storage).2+2≤_
    apply Nat.add_le_add_right
    exact BinaryFraction.countedLE_work _ _ (Y+1) (BinaryRational.storage_width _ Y (hY x hx))
      (BinaryRational.storage_width _ Y (by rw [BinaryRational.ofRat_value]; exact rationalHeight_zero.mono (Nat.zero_le _)))
      (BinaryRational.storage_denominator_pos _) (BinaryRational.storage_denominator_pos _)
  have hA' : a.2≤1+m*(3400*(Y+2)^3+5) := (countedBinaryFilter_work _ l _ hTest).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) 1)
  have hC : c.2≤1+2*m := (countedListLength_work a.1).le.trans (by omega)
  have hD : d.2≤1+2*m := (countedListLength_work l).le.trans (by omega)
  have hc : RationalHeight (c.1:BinaryRational).value M := by
    rw [show (c.1:BinaryRational).value=(c.1:ℚ) from BinaryRational.ofRat_value _,countedListLength_value]
    exact rationalHeight_natCast _ _ (hA.trans (hl.trans hm))
  have hd : RationalHeight (d.1:BinaryRational).value M := by
    rw [show (d.1:BinaryRational).value=(d.1:ℚ) from BinaryRational.ofRat_value _,countedListLength_value]
    exact rationalHeight_natCast _ _ (hl.trans hm)
  have hQ : q.2≤3600*(M+2)^3 := BinaryRational.countedOperation_work .div _ _ M hc hd
  change a.2+c.2+d.2+q.2+10≤_
  unfold binaryRowProbabilityWorkBound
  omega

def countedBinaryPlannerProbabilities {n : ℕ} (rows : Vector (List BinaryRational) n) :
    Vector (BinaryRational × ℕ) n × ℕ :=
  let a := Vector.ofFn (fun i => countedBinaryRowProbability (rows.get i))
  (a,(∑ i : Fin n,(a.get i).2)+3*n+1)

lemma countedBinaryPlannerProbabilities_value {n : ℕ} (rows : Vector (List BinaryRational) n) (i : Fin n) :
    plannerProbabilityRead (countedBinaryPlannerProbabilities rows).1 i =
      plannerProbabilityRead (countedPlannerProbabilities rows).1 i := by
  simp [countedBinaryPlannerProbabilities,countedPlannerProbabilities,plannerProbabilityRead,
    Vector.get,countedBinaryRowProbability_value]

theorem countedBinaryPlannerProbabilities_work {n : ℕ} (rows : Vector (List BinaryRational) n)
    (m Y M : ℕ) (hRows : ∀ i, (rows.get i).length≤m) (hm : m≤2^M)
    (hY : ∀ i x, x∈rows.get i → RationalHeight x.value Y) :
    (countedBinaryPlannerProbabilities rows).2≤n*binaryRowProbabilityWorkBound m Y M+3*n+1 := by
  let a := Vector.ofFn (fun i => countedBinaryRowProbability (rows.get i))
  have h (i : Fin n) : (a.get i).2≤binaryRowProbabilityWorkBound m Y M := by
    rw [show a.get i=countedBinaryRowProbability (rows.get i) from Vector.getElem_ofFn i.isLt]
    exact countedBinaryRowProbability_work _ m Y M (hRows i) hm (hY i)
  change (∑ i : Fin n,(a.get i).2)+3*n+1≤_
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _i : Fin n,binaryRowProbabilityWorkBound m Y M := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

end ProphetSecretary.Statistics
