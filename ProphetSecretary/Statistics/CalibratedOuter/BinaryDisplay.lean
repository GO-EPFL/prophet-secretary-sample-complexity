import ProphetSecretary.Analysis.BinaryRationalWork
import ProphetSecretary.Statistics.CalibratedOuter.PreparedExecution
import ProphetSecretary.Statistics.CalibratedOuter.MeshHeight

/-!
# Binary display on the outer mesh

The countdown stores the current mesh index as a binary integer. Each
comparison, index update, and arithmetic operation has a bit count.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

abbrev BinaryTaggedValue := BinaryRational × BinaryRational

def binaryTaggedValue (x : BinaryTaggedValue) : ℚ × ℚ := (x.1.value,x.2.value)

def BinaryTaggedHeight (B : ℕ) (x : BinaryTaggedValue) : Prop :=
  RationalHeight x.1.value B ∧ RationalHeight x.2.value B

def countedBinaryLE (x y : BinaryRational) : Bool × ℕ := x.storage.countedLE y.storage

lemma countedBinaryLE_value (x y : BinaryRational) :
    (countedBinaryLE x y).1 = true ↔ x.value ≤ y.value :=
  BinaryFraction.countedLE_correct _ _ x.storage_denominator_pos y.storage_denominator_pos

lemma countedBinaryLE_work (x y : BinaryRational) (B : ℕ)
    (hx : RationalHeight x.value B) (hy : RationalHeight y.value B) :
    (countedBinaryLE x y).2 ≤ 3400*(B+2)^3 :=
  BinaryFraction.countedLE_work _ _ (B+1) (x.storage_width B hx) (y.storage_width B hy)
    x.storage_denominator_pos y.storage_denominator_pos

def countedBinaryTaggedLT (x y : BinaryTaggedValue) : Bool × ℕ :=
  let a := countedBinaryLE y.1 x.1
  let b := countedBinaryLE x.1 y.1
  let c := countedBinaryLE y.2 x.2
  (!a.1 || (b.1 && !c.1),a.2+b.2+c.2+5)

lemma countedBinaryTaggedLT_value (x y : BinaryTaggedValue) :
    (countedBinaryTaggedLT x y).1 = true ↔
      (toLex (binaryTaggedValue x) : Lex (ℚ × ℚ)) < toLex (binaryTaggedValue y) := by
  have hn (a b : BinaryRational) : ((countedBinaryLE a b).1 ≠ true) ↔ b.value<a.value :=
    (not_congr (countedBinaryLE_value a b)).trans not_le
  simp only [countedBinaryTaggedLT, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, hn, countedBinaryLE_value, binaryTaggedValue, Prod.Lex.lt_iff]
  constructor
  · rintro (h|⟨h,h'⟩)
    · exact Or.inl h
    · rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h,h'⟩
  · rintro (h|⟨h,h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h.le,h'⟩

lemma countedBinaryTaggedLT_work (x y : BinaryTaggedValue) (B : ℕ)
    (hx : BinaryTaggedHeight B x) (hy : BinaryTaggedHeight B y) :
    (countedBinaryTaggedLT x y).2 ≤ 10210*(B+2)^3 := by
  have h₁ := countedBinaryLE_work y.1 x.1 B hy.1 hx.1
  have h₂ := countedBinaryLE_work x.1 y.1 B hx.1 hy.1
  have h₃ := countedBinaryLE_work y.2 x.2 B hy.2 hx.2
  have h₄ : 1≤(B+2)^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [countedBinaryTaggedLT]
  omega

private lemma binaryOpValue (op : BinaryFraction.Operation) (x y : BinaryRational) :
    (BinaryRational.countedOperation op x y).1.value =
      match op with
      | .add => x.value+y.value
      | .sub => x.value-y.value
      | .mul => x.value*y.value
      | .div => x.value/y.value
      | .minimum => min x.value y.value
      | .maximum => max x.value y.value := by
  rw [BinaryRational.countedOperation_value]
  cases op
  · exact BinaryRational.add_value _ _
  · exact BinaryRational.sub_value _ _
  · exact BinaryRational.mul_value _ _
  · exact BinaryRational.div_value _ _
  · exact BinaryRational.min_value _ _
  · exact BinaryRational.max_value _ _

private lemma binaryZeroHeight (B : ℕ) : RationalHeight (0:BinaryRational).value B := by
  rw [BinaryRational.zero_value]
  exact rationalHeight_zero.mono (Nat.zero_le _)

private lemma binaryOneHeight (B : ℕ) : RationalHeight (1:BinaryRational).value B := by
  rw [BinaryRational.one_value]
  exact rationalHeight_one.mono (Nat.zero_le _)

def countedBinaryMeshNatural : ℕ → BinaryRational × ℕ
  | 0 => (0,1)
  | n+1 =>
    let q := countedBinaryMeshNatural n
    let s := BinaryRational.countedOperation .add q.1 1
    (s.1,q.2+s.2+3)

@[simp] lemma countedBinaryMeshNatural_value (n : ℕ) :
    (countedBinaryMeshNatural n).1.value = n := by
  induction n with
  | zero => exact BinaryRational.zero_value
  | succ n ih => simp [countedBinaryMeshNatural,binaryOpValue,ih,BinaryRational.one_value,Nat.cast_succ]

lemma countedBinaryMeshNatural_work (n B : ℕ) (h : n≤2^B) :
    (countedBinaryMeshNatural n).2 ≤ (n+1)*(3610*(B+2)^3) := by
  induction n with
  | zero =>
    change 1≤1*(3610*(B+2)^3)
    exact Nat.succ_le_of_lt (by positivity)
  | succ n ih =>
    have hq : RationalHeight (countedBinaryMeshNatural n).1.value B := by
      rw [countedBinaryMeshNatural_value]
      exact rationalHeight_natCast n B (by omega)
    have hw := BinaryRational.countedOperation_work .add (countedBinaryMeshNatural n).1 1 B hq
      (binaryOneHeight B)
    have h' := ih (by omega)
    have hpos : 1≤(B+2)^3 := Nat.one_le_pow _ _ (by omega)
    rw [countedBinaryMeshNatural]
    change _≤(n+1+1)*(3610*(B+2)^3)
    rw [Nat.add_mul (n+1) 1,Nat.one_mul]
    dsimp only
    omega

def countedBinaryMeshIndex (y : BinaryRational) : ℕ → BinaryRational → BinaryRational × ℕ
  | 0, _ => (0,1)
  | k+1, j =>
    let t := countedBinaryLE j y
    if t.1 then (j,t.2+3)
    else
      let p := BinaryRational.countedOperation .sub j 1
      let q := countedBinaryMeshIndex y k p.1
      (q.1,t.2+p.2+q.2+5)

lemma countedBinaryMeshIndex_value (y : BinaryRational) (k : ℕ) (j : BinaryRational)
    (h : j.value = (k:ℚ)) :
    (countedBinaryMeshIndex y k j).1.value = ((countedMeshIndex (1:ℚ) y.value k).1 : ℚ) := by
  induction k generalizing j with
  | zero => simp [countedBinaryMeshIndex,countedMeshIndex,BinaryRational.zero_value]
  | succ k ih =>
    have hc : (countedBinaryLE j y).1=true ↔ (k:ℚ)+1≤y.value := by
      rw [countedBinaryLE_value,h,Nat.cast_add,Nat.cast_one]
    have hp : (BinaryRational.countedOperation .sub j 1).1.value = (k:ℚ) := by
      simp [binaryOpValue,h,Nat.cast_succ,BinaryRational.one_value]
    by_cases he : (countedBinaryLE j y).1=true
    · simp [countedBinaryMeshIndex,countedMeshIndex,he,hc.mp he,h]
    · simp [countedBinaryMeshIndex,countedMeshIndex,he,mt hc.mpr he,ih _ hp]

lemma countedBinaryMeshIndex_work (y : BinaryRational) (k B : ℕ) (j : BinaryRational)
    (hj : j.value = (k:ℚ)) (h : k≤2^B) (hy : RationalHeight y.value B) :
    (countedBinaryMeshIndex y k j).2 ≤ (k+1)*(7010*(B+2)^3) := by
  induction k generalizing j with
  | zero =>
    change 1≤1*(7010*(B+2)^3)
    exact Nat.succ_le_of_lt (by positivity)
  | succ k ih =>
    have hJ : RationalHeight j.value B := hj.symm ▸ rationalHeight_natCast (k+1) B h
    have hC := countedBinaryLE_work j y B hJ hy
    have hP := BinaryRational.countedOperation_work .sub j 1 B hJ (binaryOneHeight B)
    have he : (BinaryRational.countedOperation .sub j 1).1.value = (k:ℚ) := by
      simp [binaryOpValue,hj,Nat.cast_succ,BinaryRational.one_value]
    have hQ := ih _ he (by omega)
    have hpos : 1≤(B+2)^3 := Nat.one_le_pow _ _ (by omega)
    rw [countedBinaryMeshIndex]
    change _≤(k+1+1)*(7010*(B+2)^3)
    rw [Nat.add_mul (k+1) 1,Nat.one_mul]
    dsimp only
    split <;> dsimp only <;> omega

def countedBinaryUnitMesh (m : ℕ) (x : BinaryRational) : BinaryRational × ℕ :=
  let a := countedBinaryLE 1 x
  let b := countedBinaryLE x 0
  if a.1 then (1,a.2+b.2+3)
  else if b.1 then (0,a.2+b.2+4)
  else
    let M := countedBinaryMeshNatural m
    let y := BinaryRational.countedOperation .mul M.1 x
    let q := countedBinaryMeshIndex y.1 m M.1
    let d := BinaryRational.countedOperation .div 1 M.1
    let z := BinaryRational.countedOperation .mul d.1 q.1
    (z.1,a.2+b.2+M.2+y.2+q.2+d.2+z.2+10)

lemma countedBinaryUnitMesh_value (m : ℕ) (x : BinaryRational) :
    (countedBinaryUnitMesh m x).1.value=(countedMeshRound (1:ℚ) m x.value).1 := by
  have h₁ : (countedBinaryLE 1 x).1=true ↔ 1≤x.value := by rw [countedBinaryLE_value,BinaryRational.one_value]
  have h₀ : (countedBinaryLE x 0).1=true ↔ x.value≤0 := by rw [countedBinaryLE_value,BinaryRational.zero_value]
  by_cases hc : 1≤x.value
  · simp [countedBinaryUnitMesh,countedMeshRound,h₁.mpr hc,hc,BinaryRational.one_value]
  · by_cases hz : x.value≤0
    · simp [countedBinaryUnitMesh,countedMeshRound,mt h₁.mp hc,hc,h₀.mpr hz,hz,BinaryRational.zero_value]
    · simp [countedBinaryUnitMesh,countedMeshRound,mt h₁.mp hc,hc,mt h₀.mp hz,hz,
        countedBinaryMeshIndex_value _ _ _ (countedBinaryMeshNatural_value m),BinaryRational.one_value,
        binaryOpValue]

theorem countedBinaryUnitMesh_work (m P X : ℕ) (x : BinaryRational)
    (hm : m≤2^P) (hx : RationalHeight x.value X) :
    (countedBinaryUnitMesh m x).2 ≤ 30000*(m+1)*(P+X+2)^3 := by
  let B := P+X
  let M := countedBinaryMeshNatural m
  let y := BinaryRational.countedOperation .mul M.1 x
  let q := countedBinaryMeshIndex y.1 m M.1
  let d := BinaryRational.countedOperation .div 1 M.1
  have hM : RationalHeight M.1.value B := by
    simp only [M,countedBinaryMeshNatural_value]
    exact (rationalHeight_natCast m P hm).mono (by omega)
  have hX : RationalHeight x.value B := hx.mono (by omega)
  have hy : RationalHeight y.1.value B := by
    simp only [y,binaryOpValue,M,countedBinaryMeshNatural_value]
    exact (rationalHeight_natCast m P hm).mul hx
  have hd : RationalHeight d.1.value B := by
    simp only [d,binaryOpValue,BinaryRational.one_value,M,countedBinaryMeshNatural_value]
    exact (rationalHeight_one.div (rationalHeight_natCast m P hm)).mono (by omega)
  have hq : RationalHeight q.1.value B := by
    rw [show q.1.value=((countedMeshIndex 1 y.1.value m).1:ℚ) from
      countedBinaryMeshIndex_value _ _ _ (countedBinaryMeshNatural_value m)]
    exact (rationalHeight_natCast _ P ((countedMeshIndex_index_le _ _ _).trans hm)).mono (by omega)
  have hBound : m≤2^B := hm.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hA := countedBinaryLE_work 1 x B (binaryOneHeight B) hX
  have hZ := countedBinaryLE_work x 0 B hX (binaryZeroHeight B)
  have hNat := countedBinaryMeshNatural_work m B hBound
  have hMul := BinaryRational.countedOperation_work .mul M.1 x B hM hX
  have hDiv := BinaryRational.countedOperation_work .div 1 M.1 B (binaryOneHeight B) hM
  have hIndex := countedBinaryMeshIndex_work y.1 m B M.1 (countedBinaryMeshNatural_value m) hBound hy
  have hLast := BinaryRational.countedOperation_work .mul d.1 q.1 B hd hq
  have hp : 1≤(B+2)^3 := Nat.one_le_pow _ _ (by omega)
  change _≤30000*(m+1)*(B+2)^3
  unfold countedBinaryUnitMesh
  dsimp only
  split_ifs
  all_goals
    dsimp only [M,y,q,d] at hMul hDiv hIndex hLast
    nlinarith only [hA,hZ,hNat,hMul,hDiv,hIndex,hLast,hp,Nat.zero_le (m*(B+2)^3)]

def countedBinaryDisplay (m : ℕ) (H : BinaryRational) (t z : BinaryTaggedValue) :
    BinaryRational × ℕ :=
  let keep := countedBinaryTaggedLT t z
  let y := if keep.1 then z.1 else 0
  let d := BinaryRational.countedOperation .div y H
  let a := BinaryRational.countedOperation .maximum 0 d.1
  let b := BinaryRational.countedOperation .minimum a.1 1
  let q := countedBinaryUnitMesh m b.1
  (q.1,keep.2+d.2+a.2+b.2+q.2+7)

theorem countedBinaryDisplay_value (m : ℕ) (H : BinaryRational) (t z : BinaryTaggedValue) :
    (countedBinaryDisplay m H t z).1.value =
      (countedDisplay m H.value (binaryTaggedValue t) (binaryTaggedValue z)).1 := by
  have he : (if (countedBinaryTaggedLT t z).1 then z.1 else 0).value =
      countedRetention (binaryTaggedValue t) (binaryTaggedValue z) := by
    by_cases h : (countedBinaryTaggedLT t z).1=true
    · simp only [countedRetention,if_pos h,if_pos ((countedBinaryTaggedLT_value t z).mp h)]
      rfl
    · simp [countedRetention,h,mt (countedBinaryTaggedLT_value t z).mpr h,
        BinaryRational.zero_value]
  simp only [countedBinaryDisplay,countedBinaryUnitMesh_value,binaryOpValue,he,BinaryRational.zero_value,
    BinaryRational.one_value,countedDisplay]

theorem countedBinaryDisplay_work (m P B X : ℕ) (H : BinaryRational) (t z : BinaryTaggedValue)
    (hm : m≤2^P) (hH : RationalHeight H.value X) (ht : BinaryTaggedHeight B t)
    (hz : BinaryTaggedHeight B z) :
    (countedBinaryDisplay m H t z).2≤ 52000*(m+1)*(P+(B+X)+2)^3 := by
  let keep := countedBinaryTaggedLT t z
  let y : BinaryRational := if keep.1 then z.1 else 0
  let d := BinaryRational.countedOperation .div y H
  let a := BinaryRational.countedOperation .maximum 0 d.1
  let b := BinaryRational.countedOperation .minimum a.1 1
  let D := B+X
  let E := P+D
  have hY : RationalHeight y.value B := by
    dsimp only [y]
    split_ifs
    · exact hz.1
    · exact binaryZeroHeight B
  have hd : RationalHeight d.1.value D := by
    simp only [d,binaryOpValue]
    exact hY.div hH
  have ha : RationalHeight a.1.value D := by
    simp only [a,binaryOpValue,BinaryRational.zero_value]
    exact (max_choice 0 d.1.value).elim
      (fun h => h.symm ▸ rationalHeight_zero.mono (Nat.zero_le _)) (fun h => h.symm ▸ hd)
  have hb : RationalHeight b.1.value D := by
    simp only [b,binaryOpValue,BinaryRational.one_value]
    exact (min_choice a.1.value 1).elim (fun h => h.symm ▸ ha)
      (fun h => h.symm ▸ rationalHeight_one.mono (Nat.zero_le _))
  have hdW : d.2≤3600*(E+2)^3 := BinaryRational.countedOperation_work .div y H E
    (hY.mono (by omega)) (hH.mono (by omega))
  have haW : a.2≤3600*(E+2)^3 := BinaryRational.countedOperation_work .maximum 0 d.1 E
    (binaryZeroHeight E) (hd.mono (by omega))
  have hbW : b.2≤3600*(E+2)^3 := BinaryRational.countedOperation_work .minimum a.1 1 E
    (ha.mono (by omega)) (binaryOneHeight E)
  have hK := countedBinaryTaggedLT_work t z B ht hz
  have hKE : keep.2≤10210*(E+2)^3 := hK.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) _))
  have hQ : (countedBinaryUnitMesh m b.1).2≤30000*(m+1)*(E+2)^3 :=
    countedBinaryUnitMesh_work m P D b.1 hm hb
  have hp : 1≤(E+2)^3 := Nat.one_le_pow _ _ (by omega)
  change keep.2+d.2+a.2+b.2+(countedBinaryUnitMesh m b.1).2+7≤52000*(m+1)*(E+2)^3
  nlinarith only [hdW,haW,hbW,hKE,hQ,hp,Nat.zero_le (m*(E+2)^3)]

end ProphetSecretary.Statistics.Calibration
