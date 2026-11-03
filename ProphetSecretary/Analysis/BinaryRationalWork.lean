import ProphetSecretary.Analysis.BinaryRationalField

/-!
# Costs of the binary field primitives

These operations use the same storage routines as the ordered field
instance. The work includes the final canonical sign adjustment.
-/

namespace ProphetSecretary.Analysis.BinaryRational

theorem value_strictMono : StrictMono value := fun _ _ h => h

lemma canonical_normalizeSign (x : BinaryRational) : x.storage.normalizeSign=x.storage := by
  rw [x.canonical]
  unfold BinaryFraction.encode BinaryFraction.normalizeSign
  by_cases h : x.storage.value.num<0
  · have hz : x.storage.value.num.natAbs≠0 := by
      intro he
      exact h.ne (Int.natAbs_eq_zero.mp he)
    have he : x.storage.value.num.natAbs.bits.isEmpty=false := by
      apply List.isEmpty_eq_false_iff.mpr
      intro he
      have hv := binaryWordValue_bits x.storage.value.num.natAbs
      rw [he,binaryWordValue] at hv
      exact hz hv.symm
    simp [h,he]
  · simp [h]

def applyOperation (op : BinaryFraction.Operation) (x y : BinaryRational) : BinaryRational := match op with
  | .add => x+y
  | .sub => x-y
  | .mul => x*y
  | .div => x/y
  | .minimum => min x y
  | .maximum => max x y

lemma applyOperation_storage (op : BinaryFraction.Operation) (x y : BinaryRational) :
    (applyOperation op x y).storage=(op.countedEval x.storage y.storage).1.normalizeSign := by
  cases op
  · rfl
  · rfl
  · rfl
  · rfl
  · have h := BinaryFraction.countedLE_correct x.storage y.storage (storage_denominator_pos x)
      (storage_denominator_pos y)
    change (if x≤y then x else y).storage = (if (x.storage.countedLE y.storage).1 then x.storage else y.storage).normalizeSign
    by_cases he : x≤y
    · rw [if_pos he,if_pos (h.mpr he),canonical_normalizeSign]
    · rw [if_neg he,if_neg (mt h.mp he),canonical_normalizeSign]
  · have h := BinaryFraction.countedLE_correct x.storage y.storage (storage_denominator_pos x)
      (storage_denominator_pos y)
    change (if x≤y then y else x).storage = (if (x.storage.countedLE y.storage).1 then y.storage else x.storage).normalizeSign
    by_cases he : x≤y
    · rw [if_pos he,if_pos (h.mpr he),canonical_normalizeSign]
    · rw [if_neg he,if_neg (mt h.mp he),canonical_normalizeSign]

def countedOperation (op : BinaryFraction.Operation) (x y : BinaryRational) : BinaryRational × ℕ :=
  let q := op.countedEval x.storage y.storage
  (⟨q.1.normalizeSign,by rw [← applyOperation_storage]; exact (applyOperation op x y).canonical⟩,q.2+3)

lemma countedOperation_value (op : BinaryFraction.Operation) (x y : BinaryRational) :
    (countedOperation op x y).1=applyOperation op x y := by
  apply value_injective
  change (op.countedEval x.storage y.storage).1.normalizeSign.value=(applyOperation op x y).storage.value
  rw [applyOperation_storage]

theorem countedOperation_work (op : BinaryFraction.Operation) (x y : BinaryRational) (B : ℕ)
    (hx : RationalHeight x.value B) (hy : RationalHeight y.value B) :
    (countedOperation op x y).2≤3600*(B+2)^3 := by
  have h := BinaryFraction.Operation.countedEval_work op x.storage y.storage
    (storage_denominator_pos x) (storage_denominator_pos y) (B+1) (by omega)
    (storage_width x B hx) (storage_width y B hy)
  change (op.countedEval x.storage y.storage).2+3≤_
  exact (Nat.add_le_add_right h _).trans (by nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)])

theorem countedOrderTest_work (x y : BinaryRational) (B : ℕ)
    (hx : RationalHeight x.value B) (hy : RationalHeight y.value B) :
    (x.storage.countedLE y.storage).2+(y.storage.countedLE x.storage).2≤6800*(B+2)^3 := by
  have h₁ := BinaryFraction.countedLE_work x.storage y.storage (B+1)
    (storage_width x B hx) (storage_width y B hy) (storage_denominator_pos x) (storage_denominator_pos y)
  have h₂ := BinaryFraction.countedLE_work y.storage x.storage (B+1)
    (storage_width y B hy) (storage_width x B hx) (storage_denominator_pos y) (storage_denominator_pos x)
  exact (Nat.add_le_add h₁ h₂).trans_eq (by ring)

end ProphetSecretary.Analysis.BinaryRational
