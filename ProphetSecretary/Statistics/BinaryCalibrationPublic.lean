import ProphetSecretary.Statistics.BinaryCalibrationTraining

/-!
# Public calibration grids

Each grid is materialized once from its binary integer indices and the
public rational endpoints. The sample count cutoff is computed from
the width of the word for (m-1).
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis
open CalibrationBinaryExpr

lemma calibrationVectorGet_ofFn {a : Type*} {n : ℕ} (f : Fin n → a) (i : Fin n) :
    (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt

lemma calibrationVectorGet_map {a b : Type*} {n : ℕ} (f : a → b) (v : Vector a n) (i : Fin n) :
    (v.map f).get i=f (v.get i) := by simp [Vector.get]

lemma calibrationClog_eq_width (m : ℕ) : Nat.clog 2 m=(m-1).bits.length := by
  rw [Nat.size_eq_bits_len]
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    have hh := (Nat.size_le.mp (show (m-1).size≤(m-1).size from le_rfl))
    have hp : 0<(2:ℕ)^(m-1).size := by positivity
    omega
  · apply Nat.size_le.mpr
    have hh := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp (show Nat.clog 2 m≤Nat.clog 2 m from le_rfl)
    have hp : 0<(2:ℕ)^(Nat.clog 2 m) := by positivity
    omega

/-- An integer word is stored with denominator one. The work includes a
traversal of its numerator bits. -/
def countedCalibrationNat (a : ℕ) : CalibrationBinary×ℕ :=
  let x := BinaryRational.ofRat (a:ℚ)
  (x,3*x.storage.numerator.length+3)

@[simp] lemma countedCalibrationNat_value (a : ℕ) :
    (countedCalibrationNat a).1.value=(a:ℚ) := BinaryRational.ofRat_value _

lemma countedCalibrationNat_work (a B : ℕ) (h : a≤2^B) :
    (countedCalibrationNat a).2≤3*(B+1)+3 := by
  have hH : RationalHeight (countedCalibrationNat a).1.value B := by
    rw [countedCalibrationNat_value]
    exact rationalHeight_natCast a B h
  have hw := (countedCalibrationNat a).1.storage_width B hH
  have hh := (le_max_left (countedCalibrationNat a).1.storage.numerator.length
    (countedCalibrationNat a).1.storage.denominator.length).trans hw
  change 3*(countedCalibrationNat a).1.storage.numerator.length+3≤_
  omega

def binaryFamilyCoefficientExpr (zlo zhi j J : CalibrationBinary) : CalibrationBinaryExpr :=
  .node .add (.atom zlo)
    (.node .mul (.node .div (.atom j) (.atom J)) (.node .sub (.atom zhi) (.atom zlo)))

@[simp] lemma binaryFamilyCoefficientExpr_value (zlo zhi j J : CalibrationBinary) :
    (binaryFamilyCoefficientExpr zlo zhi j J).evaluate.1.value=
      zlo.value+j.value/J.value*(zhi.value-zlo.value) := by
  simp only [evaluate_value,binaryFamilyCoefficientExpr,CalibrationBinaryExpr.value,rationalCalibrationOp]

lemma binaryFamilyCoefficientExpr_work (zlo zhi j J : CalibrationBinary) (B : ℕ)
    (hlo : RationalHeight zlo.value B) (hhi : RationalHeight zhi.value B)
    (hj : RationalHeight j.value B) (hJ : RationalHeight J.value B) :
    (binaryFamilyCoefficientExpr zlo zhi j J).evaluate.2≤9*workUnit 9 B :=
  (binaryFamilyCoefficientExpr zlo zhi j J).evaluate_work 9 B ⟨hlo,⟨hj,hJ⟩,⟨hhi,hlo⟩⟩ (by rfl)

structure BinaryCalibrationPublic (m J : ℕ) where
  invM : CalibrationBinary
  muHalf : CalibrationBinary
  Lbar : CalibrationBinary
  targetGrid : Vector CalibrationBinary (4*m+1)
  familyGrid : Vector CalibrationBinary (J+1)
  work : ℕ

def BinaryCalibrationPublic.coefficient {m J : ℕ} (q : BinaryCalibrationPublic m J) (k : ℕ) :
    CalibrationBinary := q.familyGrid.get (coefficientIndex J k)

def countedBinaryCalibrationPublic (m J : ℕ) (mu zlo zhi : CalibrationBinary) :
    BinaryCalibrationPublic m J :=
  let M := countedCalibrationNat m
  let K := countedCalibrationNat J
  let R := countedCalibrationNat (4*(m-1).bits.length+2)
  let invM := BinaryRational.countedOperation .div 1 M.1
  let muHalf := BinaryRational.countedOperation .mul mu (BinaryRational.ofRat (1/2))
  let target : Vector (CalibrationBinary×ℕ) (4*m+1) := Vector.ofFn fun i =>
    let a := countedCalibrationNat i.val
    let q := BinaryRational.countedOperation .mul a.1 invM.1
    (q.1,q.2+a.2+2)
  let family : Vector (CalibrationBinary×ℕ) (J+1) := Vector.ofFn fun j =>
    let a := countedCalibrationNat j.val
    let q := (binaryFamilyCoefficientExpr zlo zhi a.1 K.1).evaluate
    (q.1,q.2+a.2+2)
  ⟨invM.1,muHalf.1,R.1,target.map Prod.fst,family.map Prod.fst,
    M.2+K.2+R.2+invM.2+muHalf.2+4*(m-1).bits.length+
    (∑ i : Fin (4*m+1),(target.get i).2)+(∑ j : Fin (J+1),(family.get j).2)+10⟩

theorem countedBinaryCalibrationPublic_value (m J : ℕ) (mu zlo zhi : CalibrationBinary) :
    let q := countedBinaryCalibrationPublic m J mu zlo zhi
    q.invM.value=(m:ℚ)⁻¹ ∧ q.muHalf.value=mu.value/2 ∧
      q.Lbar.value=4*(Nat.clog 2 m : ℚ)+2 ∧
      (∀ i : TargetGrid m,(q.targetGrid.get i).value=(i.val:ℚ)/(m:ℚ)) ∧
      (∀ k,(q.coefficient k).value=storedCalibrationCoefficient J zlo.value zhi.value k) := by
  simp only [countedBinaryCalibrationPublic,countedCalibrationOp_value,rationalCalibrationOp,
    countedCalibrationNat_value,BinaryRational.one_value,
    BinaryRational.ofRat_value,←calibrationClog_eq_width,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    BinaryCalibrationPublic.coefficient,calibrationVectorGet_map,calibrationVectorGet_ofFn,
    binaryFamilyCoefficientExpr_value,storedCalibrationCoefficient]
  refine ⟨one_div _,?_,trivial,?_,?_⟩
  · ring
  · intro i
    ring
  · intro k
    trivial

def binaryCalibrationPublicWork (m J B : ℕ) : ℕ :=
  let W := 3*(B+1)+3
  let A := 3600*(B+2)^3
  3*W+2*A+4*(B+1)+(4*m+1)*(W+A+2)+(J+1)*(W+9*workUnit 9 B+2)+10

theorem countedBinaryCalibrationPublic_work (m J : ℕ) (mu zlo zhi : CalibrationBinary) (B : ℕ)
    (hm : m≤2^B) (ht : 4*m≤2^B) (hJ : J≤2^B) (hr : 4*(m-1).bits.length+2≤2^B)
    (hmu : RationalHeight mu.value B) (hlo : RationalHeight zlo.value B)
    (hhi : RationalHeight zhi.value B) (hhalf : RationalHeight (1/2) B) :
    (countedBinaryCalibrationPublic m J mu zlo zhi).work≤binaryCalibrationPublicWork m J B := by
  let W := 3*(B+1)+3
  let A := 3600*(B+2)^3
  let M := countedCalibrationNat m
  let K := countedCalibrationNat J
  let R := countedCalibrationNat (4*(m-1).bits.length+2)
  let invM := BinaryRational.countedOperation .div 1 M.1
  let muHalf := BinaryRational.countedOperation .mul mu (BinaryRational.ofRat (1/2))
  have hMh : RationalHeight M.1.value B := by simp only [M,countedCalibrationNat_value]; exact rationalHeight_natCast _ _ hm
  have hKh : RationalHeight K.1.value B := by simp only [K,countedCalibrationNat_value]; exact rationalHeight_natCast _ _ hJ
  have hOne : RationalHeight (1:CalibrationBinary).value B := by
    rw [BinaryRational.one_value]; exact rationalHeight_one.mono (Nat.zero_le _)
  have hI : RationalHeight invM.1.value B := by
    simp only [invM,countedCalibrationOp_value,rationalCalibrationOp,BinaryRational.one_value]
    exact (rationalHeight_one.div hMh).mono (by omega)
  have hIw : invM.2≤A := BinaryRational.countedOperation_work .div _ _ B hOne hMh
  have hUw : muHalf.2≤A := BinaryRational.countedOperation_work .mul _ _ B hmu
    (by simpa only [BinaryRational.ofRat_value] using hhalf)
  have hMw : M.2≤W := countedCalibrationNat_work _ _ hm
  have hKw : K.2≤W := countedCalibrationNat_work _ _ hJ
  have hRw : R.2≤W := countedCalibrationNat_work _ _ hr
  have hLen : (m-1).bits.length≤B+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hpow : 0<(2:ℕ)^B := by positivity
    omega
  let t := fun i : Fin (4*m+1) =>
    let a := countedCalibrationNat i.val
    let q := BinaryRational.countedOperation .mul a.1 invM.1
    (q.1,q.2+a.2+2)
  let f := fun j : Fin (J+1) =>
    let a := countedCalibrationNat j.val
    let q := (binaryFamilyCoefficientExpr zlo zhi a.1 K.1).evaluate
    (q.1,q.2+a.2+2)
  have hT (i : Fin (4*m+1)) : (t i).2≤W+A+2 := by
    have h := i.isLt
    have h' : i.val≤2^B := by omega
    have ha : RationalHeight (countedCalibrationNat i.val).1.value B := by
      rw [countedCalibrationNat_value]; exact rationalHeight_natCast _ _ h'
    have hq := BinaryRational.countedOperation_work .mul _ _ B ha hI
    have hC := countedCalibrationNat_work i.val B h'
    change _≤3*(B+1)+3+3600*(B+2)^3+2
    unfold t
    dsimp only
    omega
  have hF (j : Fin (J+1)) : (f j).2≤W+9*workUnit 9 B+2 := by
    have h := j.isLt
    have h' : j.val≤2^B := by omega
    have ha : RationalHeight (countedCalibrationNat j.val).1.value B := by
      rw [countedCalibrationNat_value]; exact rationalHeight_natCast _ _ h'
    have hq := binaryFamilyCoefficientExpr_work zlo zhi _ K.1 B hlo hhi ha hKh
    have hC := countedCalibrationNat_work j.val B h'
    change _≤3*(B+1)+3+9*workUnit 9 B+2
    unfold f
    dsimp only
    omega
  have htSum : ∑ i,(t i).2≤(4*m+1)*(W+A+2) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hT i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hh
  have hfSum : ∑ j,(f j).2≤(J+1)*(W+9*workUnit 9 B+2) := by
    have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hF j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hh
  unfold countedBinaryCalibrationPublic
  simp only [calibrationVectorGet_ofFn]
  change M.2+K.2+R.2+invM.2+muHalf.2+4*(m-1).bits.length+
    (∑ i,(t i).2)+(∑ j,(f j).2)+10 ≤
    3*W+2*A+4*(B+1)+(4*m+1)*(W+A+2)+(J+1)*(W+9*workUnit 9 B+2)+10
  omega

end ProphetSecretary.Statistics.Calibration
