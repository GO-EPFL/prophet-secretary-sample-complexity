import ProphetSecretary.Statistics.BinaryCalibrationCDF
import ProphetSecretary.Statistics.BinaryCalibrationSelection

/-!
# Training statistics for binary calibration

The empirical maximum and the positive probabilities are computed on
the same stored rows. The set of active rows is extracted from the
positive probabilities and reused in validation and online queries.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis
open CalibrationBinaryExpr

variable {n m : ℕ} {TSeed : Type}

def countedBinaryRowPositive (row : List CalibrationBinary) : CalibrationBinary×ℕ :=
  let c := countedBinaryCDFCounts row 0
  let p := BinaryRational.countedOperation .sub c.1.2 c.1.1.1
  let q := BinaryRational.countedOperation .div p.1 c.1.2
  (q.1,c.2+p.2+q.2+3)

lemma countedBinaryRowPositive_value (row : List CalibrationBinary) :
    (countedBinaryRowPositive row).1.value =
      (countedPlannerRowProbability (row.map BinaryRational.value)).1 := by
  have h := countedBinaryCDFCounts_value row 0
  rw [BinaryRational.zero_value] at h
  have hl : (countedBinaryCDFCounts row 0).1.2.value =
      (countedRowCDFCounts (row.map BinaryRational.value) 0).1.2 :=
    congrArg (fun q : (ℚ×ℚ)×ℚ => q.2) h
  have hc : (countedBinaryCDFCounts row 0).1.1.1.value =
      (countedRowCDFCounts (row.map BinaryRational.value) 0).1.1.1 :=
    congrArg (fun q : (ℚ×ℚ)×ℚ => q.1.1) h
  simp only [countedBinaryRowPositive,countedCalibrationOp_value,rationalCalibrationOp,
    countedPlannerRowProbability,hl,hc]

lemma countedBinaryRowPositive_height (row : List CalibrationBinary) (P : ℕ)
    (hP : row.length≤2^P) : RationalHeight (countedBinaryRowPositive row).1.value (3*P+1) := by
  have h := countedRowCDFCounts_height (row.map BinaryRational.value) 0 P (by simpa using hP)
  rw [countedBinaryRowPositive_value,countedPlannerRowProbability]
  exact ((h.2.2.sub h.1).div h.2.2).mono (by omega)

theorem countedBinaryRowPositive_work (row : List CalibrationBinary) (B : ℕ)
    (hr : ∀ x∈row,RationalHeight x.value B) (hP : row.length≤2^B) :
    (countedBinaryRowPositive row).2≤(row.length+1)*12*calibrationFieldWork (2*B+1) := by
  have h := countedRowCDFCounts_height (row.map BinaryRational.value) 0 B (by simpa using hP)
  have hh := countedBinaryCDFCounts_value row 0
  rw [BinaryRational.zero_value] at hh
  rw [←hh] at h
  change RationalHeight (countedBinaryCDFCounts row 0).1.1.1.value B ∧
    RationalHeight (countedBinaryCDFCounts row 0).1.1.2.value B ∧
    RationalHeight (countedBinaryCDFCounts row 0).1.2.value B at h
  let A := 2*B+1
  have hBA : B≤A := by dsimp [A]; omega
  let c := countedBinaryCDFCounts row 0
  let p := BinaryRational.countedOperation .sub c.1.2 c.1.1.1
  have hzero : RationalHeight (0:CalibrationBinary).value A := by
    rw [BinaryRational.zero_value]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  have hc : c.2≤(row.length+1)*8*calibrationFieldWork A :=
    countedBinaryCDFCounts_work row 0 A hzero (fun a ha => (hr a ha).mono hBA)
      (hP.trans (Nat.pow_le_pow_right (by decide) hBA))
  have hpH : RationalHeight p.1.value A := by
    simp only [p,countedCalibrationOp_value,rationalCalibrationOp]
    exact (h.2.2.sub h.1).mono (by dsimp [A]; omega)
  have hpW : p.2≤3600*(A+2)^3 :=
    BinaryRational.countedOperation_work .sub _ _ A (h.2.2.mono hBA) (h.1.mono hBA)
  have hqW := BinaryRational.countedOperation_work .div p.1 c.1.2 A hpH (h.2.2.mono hBA)
  let W := calibrationFieldWork A
  have hW : 3600*(A+2)^3+4≤W := by dsimp [W,calibrationFieldWork]; omega
  have hs := Nat.mul_le_mul_right W (show 4≤(row.length+1)*4 by omega)
  have e : (row.length+1)*12*W=(row.length+1)*8*W+(row.length+1)*4*W := by ring
  change c.2+p.2+(BinaryRational.countedOperation .div p.1 c.1.2).2+3≤(row.length+1)*12*W
  change c.2≤(row.length+1)*8*W at hc
  rw [e]
  omega

structure BinaryTrainingStatistics (n : ℕ) where
  maximum : CalibrationBinary
  positiveCount : CalibrationBinary
  active : Finset (Fin n)
  work : ℕ

def countedBinaryTrainingStatistics (y : Fin n → Fin m → CalibrationBinary) :
    BinaryTrainingStatistics n :=
  let M := countedBinaryEmpiricalMaximum (List.ofFn fun i => List.ofFn (y i))
  let p : Array (CalibrationBinary×ℕ) := Array.ofFn fun i : Fin n => countedBinaryRowPositive (List.ofFn (y i))
  let reads := fun i : Fin n => (p[i.val]?.getD (0,0)).1
  let L := (binaryDurationSum (List.ofFn reads)).evaluate
  let tests : Array (Bool×ℕ) := Array.ofFn fun i : Fin n => countedCalibrationLT 0 (reads i)
  let A := Finset.univ.filter fun i : Fin n => (tests[i.val]?.getD (false,0)).1=true
  ⟨M.1,L.1,A,M.2+L.2+(p.toList.map fun q => q.2+2).sum+(tests.toList.map fun q => q.2+2).sum+
    6*(n+1)*(m+1)⟩

lemma binaryTrainingPositive_iff (y : Fin m → ℚ) :
    0<empiricalPositiveProbability y ↔
      (List.finRange m).any (fun a => decide (0<y a))=true := by
  unfold empiricalPositiveProbability
  simp only [List.any_eq_true,List.mem_finRange,true_and,decide_eq_true_eq]
  by_cases hm : m=0
  · subst m
    simp
  · have hm' : (0:ℚ)<(m:ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [div_pos_iff_of_pos_right hm']
    norm_cast
    simp only [Finset.card_pos,Finset.Nonempty,positiveObservations,Finset.mem_filter,Finset.mem_univ,true_and]

theorem countedBinaryTrainingStatistics_value (y : Fin n → Fin m → CalibrationBinary) :
    let q := fun i j => (y i j).value
    let a := countedBinaryTrainingStatistics y
    a.maximum.value=(countedEmpiricalMaximum (empiricalStoredRows q)).1 ∧
      a.positiveCount.value=(∑ i : Fin n,plannerProbabilityRead
        (countedPlannerProbabilities (plannerStoredRows q)).1 i) ∧
      a.active=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<q i j))=true) := by
  have hM := countedBinaryEmpiricalMaximum_value (List.ofFn fun i : Fin n => List.ofFn (y i))
  simp only [List.map_ofFn,Function.comp_def] at hM
  refine ⟨hM,?_,?_⟩
  · simp only [countedBinaryTrainingStatistics,evaluate_value,binaryDurationSum_value,
      List.map_ofFn,Function.comp_def,Array.getElem?_ofFn,Fin.isLt,dite_true,Option.getD_some,
      countedBinaryRowPositive_value,List.sum_ofFn,countedPlannerProbabilities_ofFn,countedPlannerRowProbability_ofFn]
  · ext i
    simp only [countedBinaryTrainingStatistics,Finset.mem_filter,Finset.mem_univ,true_and,
      Array.getElem?_ofFn,Fin.isLt,dite_true,Option.getD_some,countedCalibrationLT_value,
      BinaryRational.zero_value,decide_eq_true_eq,countedBinaryRowPositive_value,
      List.map_ofFn,Function.comp_def,countedPlannerRowProbability_ofFn,binaryTrainingPositive_iff]

def countedBinaryFallback (L M cutoff quarter : CalibrationBinary) : Bool×ℕ :=
  let a := countedCalibrationLT cutoff L
  let b := countedCalibrationLT quarter M
  (a.1 || b.1,a.2+b.2+2)

lemma countedBinaryFallback_value (L M cutoff quarter : CalibrationBinary) :
    (countedBinaryFallback L M cutoff quarter).1 =
      decide (cutoff.value<L.value ∨ quarter.value<M.value) := by
  apply Bool.eq_iff_iff.mpr
  simp [countedBinaryFallback]

def countedBinaryTargetMinimum (muHalf L M Lbar invM low high : CalibrationBinary)
    (grid : TargetGrid m → CalibrationBinary) (estimate : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (seed : TargetGrid m → TSeed) : CalibrationBinary×ℕ :=
  let a := countedCalibrationLE L Lbar
  let b := countedCalibrationLE muHalf M
  if a.1 && b.1 then
    let q := countedBinaryTargetScan M invM low high (List.ofFn fun j : TargetGrid m =>
      let z := grid j
      (z,estimate z (seed j)))
    (q.1,a.2+b.2+q.2+3)
  else (high,a.2+b.2+3)

theorem countedBinaryTargetMinimum_value (muHalf L M Lbar invM low high : CalibrationBinary)
    (grid : TargetGrid m → CalibrationBinary) (estimate : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (estimateQ : ℚ → TSeed → ℚ×ℕ) (he : ∀ z s,(estimate z s).1.value=(estimateQ z.value s).1)
    (seed : TargetGrid m → TSeed) (mu : ℚ) (hm : muHalf.value=mu/2)
    (hi : invM.value=1/(m:ℚ)) (hlo : low.value=1/2) (hhi : high.value=4/5)
    (hG : ∀ j,(grid j).value=(j.val:ℚ)/(m:ℚ)) :
    (countedBinaryTargetMinimum muHalf L M Lbar invM low high grid estimate seed).1.value =
      (countedTargetMinimum mu L.value M.value Lbar.value estimateQ seed).1 := by
  have aux (l : List (ℚ×ℕ)) (a : ℚ×ℕ) :
      (l.foldl (fun s q => (min s.1 q.1,s.2+q.2+2)) a).1=(l.map Prod.fst).foldl min a.1 := by
    induction l generalizing a with
    | nil => rfl
    | cons b l ih => exact ih (min a.1 b.1,a.2+b.2+2)
  unfold countedBinaryTargetMinimum countedTargetMinimum
  by_cases hL : L.value≤Lbar.value <;> by_cases hM : mu/2≤M.value
  · simp only [countedCalibrationLE_value,hm,hL,hM,decide_true,Bool.and_self,ite_true,and_self,
      countedBinaryTargetScan_value,hi,hlo,hhi,aux,List.map_ofFn,Function.comp_def,he,hG]
  · simp [hm,hL,hM,hhi]
  · simp [hm,hL,hM,hhi]
  · simp [hm,hL,hM,hhi]

theorem countedBinaryTargetMinimum_work (muHalf L M Lbar invM low high : CalibrationBinary)
    (grid : TargetGrid m → CalibrationBinary) (estimate : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (seed : TargetGrid m → TSeed) (B W : ℕ)
    (hmu : RationalHeight muHalf.value B) (hL : RationalHeight L.value B)
    (hM : RationalHeight M.value B) (hb : RationalHeight Lbar.value B) (hi : RationalHeight invM.value B)
    (hlo : RationalHeight low.value B) (hhi : RationalHeight high.value B)
    (h : ∀ j,RationalHeight (grid j).value B ∧
      RationalHeight (estimate (grid j) (seed j)).1.value B ∧ (estimate (grid j) (seed j)).2≤W) :
    (countedBinaryTargetMinimum muHalf L M Lbar invM low high grid estimate seed).2≤
      2*calibrationComparisonWork B+binaryTargetScanWork (4*m+1) B W+3 := by
  have h₁ := countedCalibrationLE_work L Lbar B hL hb
  have h₂ := countedCalibrationLE_work muHalf M B hmu hM
  let l := List.ofFn fun j : TargetGrid m => (grid j,estimate (grid j) (seed j))
  have hl : ∀ c∈l,RationalHeight c.1.value B ∧ RationalHeight c.2.1.value B ∧ c.2.2≤W := by
    intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    exact h j
  have h₃ := countedBinaryTargetScan_work M invM low high l B W hM hi hlo hhi hl
  have hlen : l.length=4*m+1 := List.length_ofFn
  rw [hlen] at h₃
  unfold countedBinaryTargetMinimum
  dsimp only
  split_ifs
  · change (countedCalibrationLE L Lbar).2+(countedCalibrationLE muHalf M).2+
      (countedBinaryTargetScan M invM low high l).2+3≤_
    omega
  · dsimp only
    omega

def binaryTrainingStatisticsWork (n m Y P : ℕ) : ℕ :=
  let B := Y+P
  let R := 3*P+1
  binaryEmpiricalMaximumWork n (n*m) Y P+(2*n+1)*workUnit (2*n+1) R+
    n*((m+1)*12*calibrationFieldWork (2*B+1)+2)+
    n*(calibrationComparisonWork R+2)+6*(n+1)*(m+1)

private lemma binaryTrainingFlatten_length (y : Fin n → Fin m → CalibrationBinary) :
    (List.ofFn fun i : Fin n => List.ofFn (y i)).flatten.length=n*m := by
  rw [List.length_flatten,List.map_ofFn]
  simp only [Function.comp_def,List.length_ofFn,List.sum_ofFn,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem countedBinaryTrainingStatistics_work (y : Fin n → Fin m → CalibrationBinary) (Y P : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (hP : m≤2^P) :
    (countedBinaryTrainingStatistics y).work≤binaryTrainingStatisticsWork n m Y P := by
  let B := Y+P
  let R := 3*P+1
  let rows := List.ofFn fun i : Fin n => List.ofFn (y i)
  let M := countedBinaryEmpiricalMaximum rows
  have hm : M.2≤binaryEmpiricalMaximumWork n (n*m) Y P := by
    have hh := countedBinaryEmpiricalMaximum_work rows Y P (by
      intro x hx
      obtain ⟨a,ha,hx⟩ := List.mem_flatten.mp hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact hY i j) (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      simpa only [List.length_ofFn] using hP)
    simpa only [M,rows,List.length_ofFn,binaryTrainingFlatten_length] using hh
  let p := fun i : Fin n => countedBinaryRowPositive (List.ofFn (y i))
  have hPB : m≤2^B := hP.trans (Nat.pow_le_pow_right (by decide) (by dsimp [B]; omega))
  have hRow (i : Fin n) : (p i).2≤(m+1)*12*calibrationFieldWork (2*B+1) := by
    have hh := countedBinaryRowPositive_work (List.ofFn (y i)) B (by
      intro a ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      exact (hY i j).mono (by dsimp [B]; omega)) (by simpa only [List.length_ofFn] using hPB)
    simpa only [p,List.length_ofFn] using hh
  have hRowH (i : Fin n) : RationalHeight (p i).1.value R :=
    countedBinaryRowPositive_height (List.ofFn (y i)) P (by simpa only [List.length_ofFn] using hP)
  let l := List.ofFn fun i : Fin n => (p i).1
  have hL : ∀ a∈l,RationalHeight a.value R := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hRowH i
  have hSum := (binaryDurationSum l).evaluate_work (2*n+1) R
    (binaryDurationSum_leaves l R hL) (by simp only [binaryDurationSum_size,l,List.length_ofFn,le_refl])
  rw [binaryDurationSum_size,List.length_ofFn] at hSum
  have hZero : RationalHeight (0:CalibrationBinary).value R := by
    rw [BinaryRational.zero_value]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  have hTest (i : Fin n) : (countedCalibrationLT 0 (p i).1).2≤calibrationComparisonWork R :=
    countedCalibrationLT_work 0 (p i).1 R hZero (hRowH i)
  have hsRow : (∑ i : Fin n,((p i).2+2))≤n*((m+1)*12*calibrationFieldWork (2*B+1)+2) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => Nat.add_le_add_right (hRow i) 2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hh
  have hsTest : (∑ i : Fin n,((countedCalibrationLT 0 (p i).1).2+2))≤n*(calibrationComparisonWork R+2) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => Nat.add_le_add_right (hTest i) 2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hh
  unfold countedBinaryTrainingStatistics
  simp only [Array.getElem?_ofFn,Fin.isLt,dite_true,Option.getD_some,Array.toList_ofFn,List.map_ofFn,
    Function.comp_def,List.sum_ofFn]
  change M.2+(binaryDurationSum l).evaluate.2+(∑ i : Fin n,((p i).2+2))+
    (∑ i : Fin n,((countedCalibrationLT 0 (p i).1).2+2))+6*(n+1)*(m+1)≤_
  change _≤binaryEmpiricalMaximumWork n (n*m) Y P+(2*n+1)*workUnit (2*n+1) R+
    n*((m+1)*12*calibrationFieldWork (2*B+1)+2)+
    n*(calibrationComparisonWork R+2)+6*(n+1)*(m+1)
  omega

theorem countedBinaryTrainingStatistics_height (y : Fin n → Fin m → CalibrationBinary) (Y P : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (hP : m≤2^P) :
    RationalHeight (countedBinaryTrainingStatistics y).maximum.value
      (binaryEmpiricalMaximumWidth n (n*m) Y P) ∧
    RationalHeight (countedBinaryTrainingStatistics y).positiveCount.value ((2*n+1)*(3*P+2)) := by
  let rows := List.ofFn fun i : Fin n => List.ofFn (y i)
  let rowsQ := rows.map (List.map BinaryRational.value)
  have hM := countedEmpiricalMaximum_height rowsQ P Y (by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
    simpa only [List.length_map,List.length_ofFn] using hP) (by
    intro a ha
    have hMap : rowsQ.flatten=(List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => (y i j).value).flatten := by
      simp only [rowsQ,rows,List.map_ofFn,Function.comp_def]
    rw [hMap] at ha
    obtain ⟨u,hu,ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact hY i j)
  let l := List.ofFn fun i : Fin n => (countedBinaryRowPositive (List.ofFn (y i))).1
  have hL : ∀ a∈l,RationalHeight a.value (3*P+1) := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact countedBinaryRowPositive_height _ _ (by simpa only [List.length_ofFn] using hP)
  have hsum := (binaryDurationSum l).value_height (3*P+1)
    (binaryDurationSum_leaves l (3*P+1) hL)
  rw [binaryDurationSum_size,List.length_ofFn] at hsum
  constructor
  · change RationalHeight (countedBinaryEmpiricalMaximum rows).1.value _
    rw [countedBinaryEmpiricalMaximum_value]
    change RationalHeight (countedEmpiricalMaximum rowsQ).1 _
    have hRows : rowsQ.length=n := by simp [rowsQ,rows]
    have hFlat : rowsQ.flatten.length=n*m := by
      rw [List.length_flatten,List.map_map]
      simp only [rows,List.map_ofFn,Function.comp_def,List.length_map,List.length_ofFn,List.sum_ofFn,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    rw [hRows,hFlat] at hM
    exact hM.mono (by unfold binaryEmpiricalMaximumWidth; nlinarith)
  · unfold countedBinaryTrainingStatistics
    simp only [Array.getElem?_ofFn,Fin.isLt,dite_true,Option.getD_some]
    change RationalHeight (binaryDurationSum l).evaluate.1.value _
    rw [evaluate_value]
    exact hsum

end ProphetSecretary.Statistics.Calibration
