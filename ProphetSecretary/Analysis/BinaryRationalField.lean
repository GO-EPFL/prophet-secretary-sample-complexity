import ProphetSecretary.Analysis.BinaryRational
import Mathlib.Algebra.Order.Field.Subfield

/-!
# Exact ordered field operations on the binary carrier

Generic planner loops can use this carrier without changing their control
structure. Field laws are transferred along the injective rational value
map, while the operations themselves use the binary storage algorithms.
-/

namespace ProphetSecretary.Analysis.BinaryRational

instance : Zero BinaryRational := ⟨ofRat 0⟩
instance : One BinaryRational := ⟨ofRat 1⟩
instance : Add BinaryRational := ⟨add⟩
instance : Sub BinaryRational := ⟨sub⟩
instance : Mul BinaryRational := ⟨mul⟩
instance : Div BinaryRational := ⟨div⟩
instance : Neg BinaryRational := ⟨fun x => sub 0 x⟩
instance : Inv BinaryRational := ⟨fun x => div 1 x⟩
instance : NatCast BinaryRational := ⟨fun n => ofRat n⟩
instance : IntCast BinaryRational := ⟨fun n => ofRat n⟩
instance : NNRatCast BinaryRational := ⟨fun q => ofRat q⟩
instance : RatCast BinaryRational := ⟨ofRat⟩
instance : SMul ℕ BinaryRational := ⟨fun n x => mul (ofRat n) x⟩
instance : SMul ℤ BinaryRational := ⟨fun n x => mul (ofRat n) x⟩
instance : SMul ℚ≥0 BinaryRational := ⟨fun q x => mul (ofRat q) x⟩
instance : SMul ℚ BinaryRational := ⟨fun q x => mul (ofRat q) x⟩

def natPower (x : BinaryRational) : ℕ → BinaryRational
  | 0 => 1
  | n+1 => mul (natPower x n) x

def intPower (x : BinaryRational) : ℤ → BinaryRational
  | .ofNat n => natPower x n
  | .negSucc n => (natPower x (n+1))⁻¹

instance : Pow BinaryRational ℕ := ⟨natPower⟩
instance : Pow BinaryRational ℤ := ⟨intPower⟩

@[simp] lemma zero_value : (0:BinaryRational).value=0 := ofRat_value 0
@[simp] lemma one_value : (1:BinaryRational).value=1 := ofRat_value 1

lemma natPower_value (x : BinaryRational) (n : ℕ) : (natPower x n).value=x.value^n := by
  induction n with
  | zero => simp [natPower]
  | succ n ih => simp [natPower,ih,pow_succ]

lemma intPower_value (x : BinaryRational) (n : ℤ) : (intPower x n).value=x.value^n := by
  cases n with
  | ofNat n =>
    change (natPower x n).value=x.value^(n:ℤ)
    rw [zpow_natCast,natPower_value]
  | negSucc n =>
    change (div 1 (natPower x (n+1))).value=x.value^(Int.negSucc n)
    rw [div_value,one_value,natPower_value,zpow_negSucc,one_div]

instance : Field BinaryRational :=
  value_injective.field value zero_value one_value add_value mul_value
    (fun x => by change (sub 0 x).value = _; rw [sub_value,zero_value,zero_sub]) sub_value
    (fun x => by change (div 1 x).value = _; rw [div_value,one_value,one_div]) div_value
    (fun n x => by change (mul (ofRat (n:ℚ)) x).value = _; rw [mul_value,ofRat_value,nsmul_eq_mul])
    (fun n x => by change (mul (ofRat (n:ℚ)) x).value = _; rw [mul_value,ofRat_value,zsmul_eq_mul])
    (fun q x => by change (mul (ofRat (q:ℚ)) x).value = _; rw [mul_value,ofRat_value,NNRat.smul_def])
    (fun q x => by change (mul (ofRat q) x).value = _; rw [mul_value,ofRat_value,Rat.smul_def]; rfl)
    natPower_value intPower_value (fun n => ofRat_value n) (fun n => ofRat_value n)
    (fun q => ofRat_value q) ofRat_value

instance : LE BinaryRational := ⟨fun x y => x.value≤y.value⟩
instance : LT BinaryRational := ⟨fun x y => x.value<y.value⟩

instance : DecidableLE BinaryRational := fun x y =>
  decidable_of_iff ((x.storage.countedLE y.storage).1=true)
    (BinaryFraction.countedLE_correct _ _ (storage_denominator_pos x) (storage_denominator_pos y))

instance : DecidableLT BinaryRational := fun x y =>
  decidable_of_iff (¬y≤x) (show ¬y.value≤x.value ↔ x.value<y.value from not_le)

instance : DecidableEq BinaryRational := fun x y =>
  decidable_of_iff (x≤y ∧ y≤x) ⟨fun h => value_injective (le_antisymm h.1 h.2),fun h => by
    subst y
    exact ⟨(show x.value≤x.value from le_rfl),(show x.value≤x.value from le_rfl)⟩⟩

instance : Max BinaryRational := ⟨fun x y => if x≤y then y else x⟩
instance : Min BinaryRational := ⟨fun x y => if x≤y then x else y⟩
instance : Ord BinaryRational := ⟨fun x y => compareOfLessAndEq x y⟩

lemma min_value (x y : BinaryRational) : (min x y).value=min x.value y.value := by
  change (if x≤y then x else y).value = _
  split_ifs with h
  · exact (min_eq_left (show x.value≤y.value from h)).symm
  · exact (min_eq_right (le_of_not_ge (show ¬x.value≤y.value from h))).symm

lemma max_value (x y : BinaryRational) : (max x y).value=max x.value y.value := by
  change (if x≤y then y else x).value = _
  split_ifs with h
  · exact (max_eq_right (show x.value≤y.value from h)).symm
  · exact (max_eq_left (le_of_not_ge (show ¬x.value≤y.value from h))).symm

lemma compare_value (x y : BinaryRational) : compare x.value y.value=compare x y := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq]
  change compareOfLessAndEq x.value y.value=compareOfLessAndEq x y
  unfold compareOfLessAndEq
  by_cases h : x<y
  · have h' : x.value<y.value := h
    simp only [if_pos h,if_pos h']
  · have h' : ¬x.value<y.value := h
    simp only [if_neg h,if_neg h',value_injective.eq_iff]

instance : LinearOrder BinaryRational :=
  Function.Injective.linearOrder value value_injective .rfl .rfl min_value max_value compare_value

instance : IsStrictOrderedRing BinaryRational :=
  Function.Injective.isStrictOrderedRing value zero_value one_value add_value mul_value .rfl .rfl

/-- The exact mathematical interpretation of the stored field. -/
def valueHom : BinaryRational →+* ℚ where
  toFun := value
  map_zero' := zero_value
  map_one' := one_value
  map_add' := add_value
  map_mul' := mul_value

end ProphetSecretary.Analysis.BinaryRational
