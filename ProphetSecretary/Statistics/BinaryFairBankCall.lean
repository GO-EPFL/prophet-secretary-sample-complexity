import ProphetSecretary.Statistics.BinaryScalarQuery
import ProphetSecretary.Statistics.FiniteFairBankCall

/-!
# A bounded fair-bank call with measured binary work

The capped level search, scalar trees, and median run on the binary
carrier. The confidence level is a public parameter of the bank shape.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

def countedBinaryHalfSearch (ρ a : BinaryRational) : ℕ → ℕ × ℕ
  | 0 => (0,1)
  | R+1 =>
    let c := a.storage.countedLE ρ.storage
    if c.1 then (0,c.2+2) else
      let z := BinaryRational.countedOperation .div a 2
      let q := countedBinaryHalfSearch ρ z.1 R
      (q.1+1,c.2+z.2+q.2+5)

lemma countedBinaryHalfSearch_value (ρ a : BinaryRational) (R : ℕ) :
    (countedBinaryHalfSearch ρ a R).1=(countedHalfPrecisionSearch ρ.value a.value R).1 := by
  induction R generalizing a with
  | zero => rfl
  | succ R ih =>
    have h : (a.storage.countedLE ρ.storage).1=true ↔ a.value≤ρ.value :=
      BinaryFraction.countedLE_correct _ _ (BinaryRational.storage_denominator_pos a)
        (BinaryRational.storage_denominator_pos ρ)
    have hZ : (BinaryRational.countedOperation .div a 2).1.value=a.value/2 := by
      rw [BinaryRational.countedOperation_value]
      change (BinaryRational.div a 2).value = _
      rw [BinaryRational.div_value,show (2:BinaryRational).value=(2:ℚ) from BinaryRational.ofRat_value 2]
    by_cases he : a.value≤ρ.value
    · simp only [countedBinaryHalfSearch,countedHalfPrecisionSearch,if_pos (h.mpr he),if_pos he]
    · simp only [countedBinaryHalfSearch,countedHalfPrecisionSearch,if_neg (mt h.mp he),if_neg he,ih,hZ]

theorem countedBinaryHalfSearch_work (ρ a : BinaryRational) (R H A : ℕ)
    (hρ : RationalHeight ρ.value H) (ha : RationalHeight a.value A) :
    (countedBinaryHalfSearch ρ a R).2≤1+R*(7000*(H+A+R+4)^3+5) := by
  induction R generalizing a A with
  | zero => simp [countedBinaryHalfSearch]
  | succ R ih =>
    let B := H+A+(R+1)+2
    let c := a.storage.countedLE ρ.storage
    let z := BinaryRational.countedOperation .div a 2
    have ha' : RationalHeight a.value B := ha.mono (by dsimp [B]; omega)
    have hρ' : RationalHeight ρ.value B := hρ.mono (by dsimp [B]; omega)
    have h2 : RationalHeight (2:BinaryRational).value 1 := by
      rw [show (2:BinaryRational).value=(2:ℚ) from BinaryRational.ofRat_value 2]
      exact rationalHeight_natCast 2 1 (by decide)
    have hc : c.2≤3400*(B+2)^3 := BinaryFraction.countedLE_work _ _ (B+1)
      (BinaryRational.storage_width _ B ha') (BinaryRational.storage_width _ B hρ')
      (BinaryRational.storage_denominator_pos _) (BinaryRational.storage_denominator_pos _)
    have hz : z.2≤3600*(B+2)^3 := BinaryRational.countedOperation_work .div _ _ B ha'
      (h2.mono (by dsimp [B]; omega))
    have hZ : RationalHeight z.1.value (A+1) := by
      rw [BinaryRational.countedOperation_value]
      change RationalHeight (BinaryRational.div a 2).value _
      rw [BinaryRational.div_value]
      exact ha.div h2
    have hq := ih z.1 (A+1) hZ
    have he : H+(A+1)+R+4=B+2 := by dsimp [B]; omega
    rw [he] at hq
    unfold countedBinaryHalfSearch
    dsimp only
    split_ifs
    · change c.2+2≤1+(R+1)*(7000*(B+2)^3+5)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · change c.2+z.2+(countedBinaryHalfSearch ρ z.1 R).2+5≤1+(R+1)*(7000*(B+2)^3+5)
      rw [Nat.add_mul,Nat.one_mul]
      omega

def countedBinaryPrecisionRatio (β h : BinaryRational) : BinaryRational × ℕ :=
  let a := BinaryRational.countedOperation .div h 2
  let b := BinaryRational.countedOperation .mul a.1 a.1
  let c := BinaryRational.countedOperation .mul β β
  let d := BinaryRational.countedOperation .mul 1600 c.1
  let q := BinaryRational.countedOperation .div b.1 d.1
  (q.1,a.2+b.2+c.2+d.2+q.2+8)

lemma countedBinaryPrecisionRatio_value (β h : BinaryRational) :
    (countedBinaryPrecisionRatio β h).1.value=scalarPlannerPrecisionRatio β.value (h.value/2) := by
  simp only [countedBinaryPrecisionRatio,BinaryRational.countedOperation_value,BinaryRational.applyOperation]
  change (BinaryRational.div (BinaryRational.mul (BinaryRational.div h 2) (BinaryRational.div h 2))
    (BinaryRational.mul 1600 (BinaryRational.mul β β))).value = _
  simp only [BinaryRational.div_value,BinaryRational.mul_value,
    show (2:BinaryRational).value=(2:ℚ) from BinaryRational.ofRat_value 2,
    show (1600:BinaryRational).value=(1600:ℚ) from BinaryRational.ofRat_value 1600,
    scalarPlannerPrecisionRatio,pow_two]

lemma countedBinaryPrecisionRatio_height (β h : BinaryRational) (W A : ℕ)
    (hβ : RationalHeight β.value W) (hh : RationalHeight h.value A) :
    RationalHeight (countedBinaryPrecisionRatio β h).1.value (2*A+2*W+13) := by
  rw [countedBinaryPrecisionRatio_value]
  have h2 : RationalHeight (2:ℚ) 1 := rationalHeight_natCast 2 1 (by decide)
  exact (scalarPlannerPrecisionRatio_height hβ (hh.div h2)).mono (by omega)

private lemma binaryRatioOpValue (op : BinaryFraction.Operation) (x y : BinaryRational) :
    (BinaryRational.countedOperation op x y).1.value=op.eval x.value y.value := by
  change (op.countedEval x.storage y.storage).1.normalizeSign.value = _
  rw [BinaryFraction.normalizeSign_value]
  exact (BinaryFraction.Operation.countedEval_correct op _ _ (BinaryRational.storage_denominator_pos x)
    (BinaryRational.storage_denominator_pos y)).1

theorem countedBinaryPrecisionRatio_work (β h : BinaryRational) (W A : ℕ)
    (hβ : RationalHeight β.value W) (hh : RationalHeight h.value A) :
    (countedBinaryPrecisionRatio β h).2≤5*(3600*(2*A+2*W+15)^3)+8 := by
  let B := 2*A+2*W+13
  let C := 3600*(B+2)^3
  let a := BinaryRational.countedOperation .div h 2
  let b := BinaryRational.countedOperation .mul a.1 a.1
  let c := BinaryRational.countedOperation .mul β β
  let d := BinaryRational.countedOperation .mul 1600 c.1
  let q := BinaryRational.countedOperation .div b.1 d.1
  have h2 : RationalHeight (2:BinaryRational).value 1 := by
    rw [show (2:BinaryRational).value=(2:ℚ) from BinaryRational.ofRat_value 2]
    exact rationalHeight_natCast 2 1 (by decide)
  have h1600 : RationalHeight (1600:BinaryRational).value 11 := by
    rw [show (1600:BinaryRational).value=(1600:ℚ) from BinaryRational.ofRat_value 1600]
    exact rationalHeight_natCast 1600 11 (by decide)
  have ha : RationalHeight a.1.value (A+1) := by rw [binaryRatioOpValue]; exact hh.div h2
  have hb : RationalHeight b.1.value (2*A+2) := by rw [binaryRatioOpValue]; exact (ha.mul ha).mono (by omega)
  have hc : RationalHeight c.1.value (2*W) := by rw [binaryRatioOpValue]; exact (hβ.mul hβ).mono (by omega)
  have hd : RationalHeight d.1.value (2*W+11) := by rw [binaryRatioOpValue]; exact (h1600.mul hc).mono (by omega)
  have haW : a.2≤C := BinaryRational.countedOperation_work .div _ _ B (hh.mono (by dsimp [B]; omega))
    (h2.mono (by dsimp [B]; omega))
  have hbW : b.2≤C := BinaryRational.countedOperation_work .mul _ _ B (ha.mono (by dsimp [B]; omega))
    (ha.mono (by dsimp [B]; omega))
  have hcW : c.2≤C := BinaryRational.countedOperation_work .mul _ _ B (hβ.mono (by dsimp [B]; omega))
    (hβ.mono (by dsimp [B]; omega))
  have hdW : d.2≤C := BinaryRational.countedOperation_work .mul _ _ B (h1600.mono (by dsimp [B]; omega))
    (hc.mono (by dsimp [B]; omega))
  have hqW : q.2≤C := BinaryRational.countedOperation_work .div _ _ B (hb.mono (by dsimp [B]; omega))
    (hd.mono (by dsimp [B]; omega))
  change a.2+b.2+c.2+d.2+q.2+8≤5*C+8
  omega

variable {n m : ℕ}

def countedBinaryCalibrationRows (y : Fin n → Fin m → BinaryRational) : Vector (List BinaryRational) n × ℕ :=
  let v := Vector.ofFn (fun i => List.ofFn (fun j => countedBinaryClamp 0 1 (y i j)))
  (v.map (List.map Prod.fst), (∑ i : Fin n, ((v.get i).map Prod.snd).sum)+6*n*(m+1)+2)

private lemma binaryCalibVectorGet {α : Type*} {N : ℕ} (f : Fin N → α) (i : Fin N) :
    (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt

lemma countedBinaryCalibrationRows_get (y : Fin n → Fin m → BinaryRational) (i : Fin n) :
    (countedBinaryCalibrationRows y).1.get i=List.ofFn (fun j => (countedBinaryClamp 0 1 (y i j)).1) := by
  simp [countedBinaryCalibrationRows,Vector.get,List.map_ofFn,Function.comp_def]

lemma countedBinaryCalibrationRows_value (y : Fin n → Fin m → BinaryRational) :
    plannerRowsValueMap BinaryRational.value (countedBinaryCalibrationRows y).1 =
      calibrationStoredRows (fun i j => (y i j).value) := by
  apply Vector.ext
  intro i hi
  let k : Fin n := ⟨i,hi⟩
  change (plannerRowsValueMap BinaryRational.value (countedBinaryCalibrationRows y).1).get k = _
  have he : (plannerRowsValueMap BinaryRational.value (countedBinaryCalibrationRows y).1).get k =
      ((countedBinaryCalibrationRows y).1.get k).map BinaryRational.value := by simp [plannerRowsValueMap,Vector.get]
  rw [he,countedBinaryCalibrationRows_get,List.map_ofFn]
  change List.ofFn (fun j => (countedBinaryClamp 0 1 (y k j)).1.value) =
    (calibrationStoredRows (fun i j => (y i j).value)).get k
  simp only [calibrationStoredRows,plannerStoredRows_get,countedBinaryClamp_value,
    BinaryRational.max_value,BinaryRational.min_value,BinaryRational.zero_value,BinaryRational.one_value]

def countedBinaryFairBankCall (y : Fin n → Fin m → BinaryRational) (x : ScalarPlannerListState n BinaryRational)
    (b R a : ℕ) (h : BinaryRational) (seed : FairQueryBank n b (2*a+1) R) : MedianCopiesResult BinaryRational :=
  let rows := countedBinaryCalibrationRows y
  let prep := countedBinaryPlannerProbabilities rows.1
  let f := countedBinaryPlannerFrame (plannerProbabilityRead prep.1) x
  let tol := countedBinaryPrecisionRatio f.1.weight h
  let q := countedBinaryHalfSearch tol.1 1 R
  let j : Fin (R+1) := ⟨q.1, by
    rw [countedBinaryHalfSearch_value]
    exact Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  let v := countedBinaryScalarQueryAtLevel rows.1 x b j.val a (seed j)
  {v with work := rows.2+prep.2+f.2+tol.2+q.2+v.work+8}

theorem countedBinaryFairBankCall_value (y : Fin n → Fin m → BinaryRational) (x : ScalarPlannerListState n BinaryRational)
    (b R : ℕ) (h : BinaryRational) (p : ℚ) (H : ∃ j : ℕ, (1/4:ℚ)^j≤p)
    (seed : FairQueryBank n b (confidenceCopyCount p H) R) :
    (countedBinaryFairBankCall y x b R (countedConfidenceLevel p H).1 h seed).value.value =
      (countedRationalFairBankCall (fun i j => (y i j).value) (scalarPlannerStateValueMap BinaryRational.value x)
        b R h.value p H seed).value := by
  let rows := (countedBinaryCalibrationRows y).1
  let rows' := calibrationStoredRows (fun i j => (y i j).value)
  let pr := plannerProbabilityRead (countedBinaryPlannerProbabilities rows).1
  let f := (countedBinaryPlannerFrame pr x).1
  let x' := scalarPlannerStateValueMap BinaryRational.value x
  let β := storedScalarPlannerWeight rows' x'
  have hRows : plannerRowsValueMap BinaryRational.value rows=rows' := countedBinaryCalibrationRows_value y
  have hp : plannerProbabilityRead (countedPlannerProbabilities rows').1=fun i => (pr i).value := by
    rw [← hRows]
    funext i
    exact (plannerProbabilityRead_valueMap BinaryRational.valueHom BinaryRational.value_strictMono rows i).trans
      (congrArg BinaryRational.value (countedBinaryPlannerProbabilities_value rows i).symm)
  have hF := countedScalarPlannerFrame_valueMap BinaryRational.valueHom BinaryRational.value_strictMono pr x
  have hβ : f.weight.value=β := by
    change f.weight.value=(countedScalarPlannerFrame (plannerProbabilityRead (countedPlannerProbabilities rows').1) x').1.weight
    rw [hp]
    rw [← countedBinaryPlannerFrame_value] at hF
    exact (congrArg ScalarPlannerFrame.weight hF).symm
  let ρ := (countedBinaryPrecisionRatio f.weight h).1
  let j : Fin (R+1) := ⟨(countedBinaryHalfSearch ρ 1 R).1, by
    rw [countedBinaryHalfSearch_value]
    exact Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  let j' : Fin (R+1) := ⟨(countedHalfPrecisionSearch (scalarPlannerPrecisionRatio β (h.value/2)) 1 R).1,
    Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  have hJ : j=j' := by
    apply Fin.ext
    change (countedBinaryHalfSearch ρ 1 R).1=(countedHalfPrecisionSearch (scalarPlannerPrecisionRatio β (h.value/2)) 1 R).1
    rw [countedBinaryHalfSearch_value,BinaryRational.one_value,countedBinaryPrecisionRatio_value,hβ]
  change (countedBinaryScalarQueryAtLevel rows x b j.val (countedConfidenceLevel p H).1 (seed j)).value.value =
    (countedRationalFairQueryAtLevel rows' x' j'.val p H b (seed j')).value
  rw [countedBinaryScalarQueryAtLevel_value,hRows,hJ]

theorem countedBinaryFairBankCall_height (y : Fin n → Fin m → BinaryRational)
    (x : ScalarPlannerListState n BinaryRational) (b R : ℕ) (h : BinaryRational) (p : ℚ)
    (H : ∃ j : ℕ, (1/4:ℚ)^j≤p) (seed : FairQueryBank n b (confidenceCopyCount p H) R)
    (Y M U Z : ℕ) (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j).value Y)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z) (hZ : 2≤Z) :
    RationalHeight (countedBinaryFairBankCall y x b R (countedConfidenceLevel p H).1 h seed).value.value
      (finiteFairBankOutputHeight n m Y M U Z b R) := by
  rw [countedBinaryFairBankCall_value]
  exact countedRationalFairBankCall_height (fun i j => (y i j).value) (scalarPlannerStateValueMap BinaryRational.value x)
    hx b R h.value p H seed Y M U Z hm hy hu hz hZ

def binaryCalibrationRowsWorkBound (n m Y : ℕ) : ℕ :=
  n*m*(2*(3600*(Y+2)^3)+2)+6*n*(m+1)+2

theorem countedBinaryCalibrationRows_work (y : Fin n → Fin m → BinaryRational) (Y : ℕ)
    (hy : ∀ i j, RationalHeight (y i j).value Y) :
    (countedBinaryCalibrationRows y).2≤binaryCalibrationRowsWorkBound n m Y := by
  let v := Vector.ofFn (fun i => List.ofFn (fun j => countedBinaryClamp 0 1 (y i j)))
  let W := 2*(3600*(Y+2)^3)+2
  have h0 : RationalHeight (0:BinaryRational).value Y := by
    rw [BinaryRational.zero_value]; exact rationalHeight_zero.mono (Nat.zero_le _)
  have h1 : RationalHeight (1:BinaryRational).value Y := by
    rw [BinaryRational.one_value]; exact rationalHeight_one.mono (Nat.zero_le _)
  have h (i : Fin n) : ((v.get i).map Prod.snd).sum≤m*W := by
    rw [show v.get i=List.ofFn (fun j => countedBinaryClamp 0 1 (y i j)) from binaryCalibVectorGet _ _]
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    calc
      _ ≤ ∑ _j : Fin m,W := Finset.sum_le_sum (fun j _ => countedBinaryClamp_work _ _ _ Y h0 h1 (hy i j))
      _ = _ := by simp
  have hS : (∑ i : Fin n,((v.get i).map Prod.snd).sum)≤n*(m*W) := by
    calc
      _ ≤ ∑ _i : Fin n,m*W := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp
  change (∑ i : Fin n,((v.get i).map Prod.snd).sum)+6*n*(m+1)+2≤_
  exact (Nat.add_le_add_right (Nat.add_le_add_right hS _) _).trans_eq (by
    unfold binaryCalibrationRowsWorkBound W
    ring)

def binaryFairBankWorkBound (n m Y M U Z b R a H : ℕ) : ℕ :=
  let W := n*(2*M+3)
  let D := 2*H+2*W+13
  binaryCalibrationRowsWorkBound n m Y + n*binaryRowProbabilityWorkBound m Y M+3*n+1+
    binaryFrameWorkBound n (2*M) U Z+5*(3600*(D+2)^3)+8 +
    (1+R*(7000*(D+R+4)^3+5))+binaryScalarQueryWorkBound n m Y M U Z b R a+8

theorem countedBinaryFairBankCall_work (y : Fin n → Fin m → BinaryRational) (x : ScalarPlannerListState n BinaryRational)
    (b R a : ℕ) (h : BinaryRational) (seed : FairQueryBank n b (2*a+1) R)
    (Y M U Z H : ℕ) (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j).value Y)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z) (hZ : 2≤Z)
    (hh : RationalHeight h.value H) :
    (countedBinaryFairBankCall y x b R a h seed).work≤binaryFairBankWorkBound n m Y M U Z b R a H := by
  let W := n*(2*M+3)
  let D := 2*H+2*W+13
  let rows := countedBinaryCalibrationRows y
  let prep := countedBinaryPlannerProbabilities rows.1
  let p := plannerProbabilityRead prep.1
  let f := countedBinaryPlannerFrame p x
  let ρ := countedBinaryPrecisionRatio f.1.weight h
  let q := countedBinaryHalfSearch ρ.1 1 R
  let j : Fin (R+1) := ⟨q.1, by
    rw [countedBinaryHalfSearch_value]
    exact Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  have hRows (i : Fin n) : (rows.1.get i).length≤m := by
    rw [countedBinaryCalibrationRows_get,List.length_ofFn]
  have hY (i : Fin n) (u : BinaryRational) (hu' : u∈rows.1.get i) : RationalHeight u.value Y := by
    rw [countedBinaryCalibrationRows_get] at hu'
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hu'
    rw [countedBinaryClamp_value,BinaryRational.max_value,BinaryRational.min_value,
      BinaryRational.zero_value,BinaryRational.one_value]
    exact rationalHeight_unitClamp (hy i k)
  have hPrep : prep.2≤n*binaryRowProbabilityWorkBound m Y M+3*n+1 :=
    countedBinaryPlannerProbabilities_work rows.1 m Y M hRows hm hY
  have hp (i : Fin n) : RationalHeight (p i).value (2*M) := by
    have he : p i=(countedBinaryRowProbability (rows.1.get i)).1 := by
      simp [p,prep,plannerProbabilityRead,countedBinaryPlannerProbabilities,Vector.get]
    rw [he]
    exact countedBinaryRowProbability_height (rows.1.get i) M ((hRows i).trans hm)
  have hf : f.2≤binaryFrameWorkBound n (2*M) U Z := countedBinaryPlannerFrame_work p x (2*M) U Z hx hp hu hz hZ
  have hW : RationalHeight f.1.weight.value W := by
    change RationalHeight (countedBinaryPlannerWeight p (countedBinaryPlannerActive p x.1).1).1.value _
    have hL : x.1.length≤n := by
      simpa only [List.toFinset_card_of_nodup hx,Fintype.card_fin] using Finset.card_le_univ x.1.toFinset
    have hA : (countedBinaryPlannerActive p x.1).1.length≤n := by
      rw [countedBinaryPlannerActive_value]
      exact (countedPlannerActive_length p x.1).trans hL
    exact (countedBinaryPlannerWeight_height p _ (2*M) hp).mono (Nat.mul_le_mul_right _ hA)
  have hρ : ρ.2≤5*(3600*(D+2)^3)+8 := countedBinaryPrecisionRatio_work f.1.weight h W H hW hh
  have hρH : RationalHeight ρ.1.value D := countedBinaryPrecisionRatio_height f.1.weight h W H hW hh
  have hq : q.2≤1+R*(7000*(D+R+4)^3+5) := by
    have h1 : RationalHeight (1:BinaryRational).value 0 := by rw [BinaryRational.one_value]; exact rationalHeight_one
    simpa only [Nat.add_zero] using countedBinaryHalfSearch_work ρ.1 1 R D 0 hρH h1
  have hR : j.val≤R := Nat.le_of_lt_succ j.isLt
  have hV := countedBinaryScalarQueryAtLevel_work rows.1 x b j.val a R m Y M U Z (seed j)
    hR hm hRows hY hx hu hz hZ
  have hC : rows.2≤binaryCalibrationRowsWorkBound n m Y := countedBinaryCalibrationRows_work y Y hy
  change rows.2+prep.2+f.2+ρ.2+q.2+(countedBinaryScalarQueryAtLevel rows.1 x b j.val a (seed j)).work+8≤_
  change _≤binaryCalibrationRowsWorkBound n m Y+n*binaryRowProbabilityWorkBound m Y M+3*n+1+
    binaryFrameWorkBound n (2*M) U Z+5*(3600*(D+2)^3)+8+
    (1+R*(7000*(D+R+4)^3+5))+binaryScalarQueryWorkBound n m Y M U Z b R a+8
  omega

end ProphetSecretary.Statistics.Calibration
