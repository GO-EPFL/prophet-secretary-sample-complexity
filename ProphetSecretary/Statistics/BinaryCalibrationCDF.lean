import ProphetSecretary.Statistics.BinaryCalibrationPrimitive
import ProphetSecretary.Statistics.EmpiricalMaximumHeight

/-!
# The empirical maximum on binary rational storage

Each row scans the closed and strict counts. The products of those row
probabilities give the mass of each distinct nonnegative support value.
All comparisons, counts, divisions, products and atom sums below execute
on the stored binary rationals.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {α : Type*}

def calibrationFieldWork (B : ℕ) : ℕ := calibrationComparisonWork B+3600*(B+2)^3+4

def countedCalibrationFilter (test : α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([],1)
  | a::l =>
    let b := test a
    let t := countedCalibrationFilter test l
    (if b.1 then a::t.1 else t.1,b.2+t.2+2)

lemma countedCalibrationFilter_value (test : α → Bool × ℕ) (l : List α) :
    (countedCalibrationFilter test l).1=l.filter (fun a => (test a).1) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [countedCalibrationFilter,List.filter_cons,ih]

lemma countedCalibrationFilter_work (test : α → Bool × ℕ) (l : List α) (W : ℕ)
    (hW : ∀ a∈l,(test a).2≤W) :
    (countedCalibrationFilter test l).2≤1+l.length*(W+2) := by
  induction l with
  | nil => simp [countedCalibrationFilter]
  | cons a l ih =>
    have h := ih (fun b hb => hW b (List.mem_cons_of_mem _ hb))
    have ha := hW a List.mem_cons_self
    simp only [countedCalibrationFilter,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedCalibrationContains (a : CalibrationBinary) : List CalibrationBinary → Bool × ℕ
  | [] => (false,1)
  | b::l =>
    let q := countedCalibrationEQ a b
    let tail := countedCalibrationContains a l
    (q.1 || tail.1,q.2+tail.2+2)

lemma countedCalibrationContains_value (a : CalibrationBinary) (l : List CalibrationBinary) :
    (countedCalibrationContains a l).1=decide (a.value∈l.map BinaryRational.value) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    apply Bool.eq_iff_iff.mpr
    simp only [countedCalibrationContains,countedCalibrationEQ_value,ih,List.map_cons,List.mem_cons,Bool.or_eq_true,decide_eq_true_eq]

lemma countedCalibrationContains_work (a : CalibrationBinary) (l : List CalibrationBinary) (B : ℕ)
    (ha : RationalHeight a.value B) (hl : ∀ b∈l,RationalHeight b.value B) :
    (countedCalibrationContains a l).2≤1+l.length*(calibrationComparisonWork B+2) := by
  induction l with
  | nil => simp [countedCalibrationContains]
  | cons b l ih =>
    have he := countedCalibrationEQ_work a b B ha (hl b List.mem_cons_self)
    have h := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [countedCalibrationContains,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedCalibrationDistinct : List CalibrationBinary → List CalibrationBinary × ℕ
  | [] => ([],1)
  | a::l =>
    let t := countedCalibrationDistinct l
    let q := countedCalibrationContains a t.1
    (if q.1 then t.1 else a::t.1,t.2+q.2+2)

lemma countedCalibrationDistinct_value (l : List CalibrationBinary) :
    (countedCalibrationDistinct l).1.map BinaryRational.value =
      (countedDistinct (l.map BinaryRational.value)).1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [countedCalibrationDistinct,countedCalibrationContains_value,List.map_cons,countedDistinct,
      countedListContains_value,ih]
    split_ifs <;> simp only [ih,List.map_cons]

private lemma countedCalibrationDistinct_mem (l : List CalibrationBinary) (a : CalibrationBinary) :
    a∈(countedCalibrationDistinct l).1 → a∈l := by
  induction l with
  | nil => simp [countedCalibrationDistinct]
  | cons b l ih =>
    unfold countedCalibrationDistinct
    dsimp only
    split_ifs
    · intro ha
      exact List.mem_cons_of_mem _ (ih ha)
    · simp only [List.mem_cons]
      exact Or.imp id ih

private lemma countedCalibrationDistinct_length (l : List CalibrationBinary) :
    (countedCalibrationDistinct l).1.length≤l.length := by
  induction l with
  | nil => simp [countedCalibrationDistinct]
  | cons a l ih =>
    unfold countedCalibrationDistinct
    dsimp only
    split_ifs <;> simp only [List.length_cons] <;> omega

lemma countedCalibrationDistinct_work (l : List CalibrationBinary) (B : ℕ)
    (h : ∀ a∈l,RationalHeight a.value B) :
    (countedCalibrationDistinct l).2≤(l.length+1)^2*(calibrationComparisonWork B+4) := by
  induction l with
  | nil =>
    simp only [countedCalibrationDistinct,List.length_nil,zero_add,one_pow,one_mul]
    omega
  | cons a l ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := countedCalibrationContains_work a (countedCalibrationDistinct l).1 B
      (h a List.mem_cons_self) (fun x hx => h x (List.mem_cons_of_mem _ (countedCalibrationDistinct_mem l x hx)))
    have hl := countedCalibrationDistinct_length l
    let K := calibrationComparisonWork B+4
    change (countedCalibrationDistinct l).2≤(l.length+1)^2*K at ht
    have hMult := Nat.mul_le_mul_right K hl
    have hC' : (countedCalibrationContains a (countedCalibrationDistinct l).1).2≤1+l.length*K :=
      hc.trans (Nat.add_le_add_left ((Nat.mul_le_mul_left _ (by omega : calibrationComparisonWork B+2≤K)).trans hMult) _)
    change (countedCalibrationDistinct l).2+
      (countedCalibrationContains a (countedCalibrationDistinct l).1).2+2≤(l.length+2)^2*K
    have hK : 4≤K := by dsimp [K]; omega
    have hExpand : (l.length+2)^2*K=(l.length+1)^2*K+l.length*K+(l.length+3)*K := by ring
    rw [hExpand]
    have hLast : 3≤(l.length+3)*K :=
      (show 3≤l.length+3 by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
    omega

def countedCalibrationSupport (rows : List (List CalibrationBinary)) : List CalibrationBinary × ℕ :=
  let f := countedFlattenRows rows
  let p := countedCalibrationFilter (fun a => countedCalibrationLT 0 a) f.1
  let d := countedCalibrationDistinct (0::p.1)
  (d.1,f.2+p.2+d.2+2)

private lemma flattenValueMap (rows : List (List CalibrationBinary)) :
    (rows.map (List.map BinaryRational.value)).flatten=rows.flatten.map BinaryRational.value := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp only [List.map_cons,List.flatten_cons,List.map_append,ih]

lemma countedCalibrationSupport_value (rows : List (List CalibrationBinary)) :
    (countedCalibrationSupport rows).1.map BinaryRational.value =
      (countedEmpiricalSupport (rows.map (List.map BinaryRational.value))).1 := by
  simp only [countedCalibrationSupport,countedEmpiricalSupport,countedCalibrationDistinct_value,
    countedCalibrationFilter_value,countedFlattenRows_value,countedPredicateFilter_value,
    countedCalibrationLT_value,List.map_cons,BinaryRational.zero_value,flattenValueMap,List.filter_map,Function.comp_def]

def countedBinaryCDFCounts (row : List CalibrationBinary) (a : CalibrationBinary) :
    ((CalibrationBinary × CalibrationBinary) × CalibrationBinary) × ℕ :=
  match row with
  | [] => (((0,0),0),3)
  | x::row =>
    let t := countedBinaryCDFCounts row a
    let l := BinaryRational.countedOperation .add t.1.2 1
    let c := countedCalibrationLT x a
    if c.1 then
      let p := BinaryRational.countedOperation .add t.1.1.1 1
      let q := BinaryRational.countedOperation .add t.1.1.2 1
      (((p.1,q.1),l.1),t.2+l.2+c.2+p.2+q.2+4)
    else
      let d := countedCalibrationLE x a
      if d.1 then
        let p := BinaryRational.countedOperation .add t.1.1.1 1
        (((p.1,t.1.1.2),l.1),t.2+l.2+c.2+d.2+p.2+4)
      else ((t.1.1,l.1),t.2+l.2+c.2+d.2+4)

private def calibrationCountsValue (q : (CalibrationBinary × CalibrationBinary) × CalibrationBinary) :
    (ℚ × ℚ) × ℚ := ((q.1.1.value,q.1.2.value),q.2.value)

lemma countedBinaryCDFCounts_value (row : List CalibrationBinary) (a : CalibrationBinary) :
    calibrationCountsValue (countedBinaryCDFCounts row a).1 =
      (countedRowCDFCounts (row.map BinaryRational.value) a.value).1 := by
  induction row with
  | nil => simp [countedBinaryCDFCounts,calibrationCountsValue,countedRowCDFCounts]
  | cons x l ih =>
    have h₁ : (countedBinaryCDFCounts l a).1.1.1.value =
        (countedRowCDFCounts (l.map BinaryRational.value) a.value).1.1.1 :=
      congrArg (fun q : (ℚ×ℚ)×ℚ => q.1.1) ih
    have h₂ : (countedBinaryCDFCounts l a).1.1.2.value =
        (countedRowCDFCounts (l.map BinaryRational.value) a.value).1.1.2 :=
      congrArg (fun q : (ℚ×ℚ)×ℚ => q.1.2) ih
    have h₃ : (countedBinaryCDFCounts l a).1.2.value =
        (countedRowCDFCounts (l.map BinaryRational.value) a.value).1.2 :=
      congrArg (fun q : (ℚ×ℚ)×ℚ => q.2) ih
    by_cases h : x.value<a.value
    · simp [countedBinaryCDFCounts,countedRowCDFCounts,h,calibrationCountsValue,
        rationalCalibrationOp,h₁,h₂,h₃]
    · by_cases h' : x.value≤a.value <;>
        simp [countedBinaryCDFCounts,countedRowCDFCounts,h,h',calibrationCountsValue,
          rationalCalibrationOp,h₁,h₂,h₃]

lemma countedBinaryCDFCounts_work (row : List CalibrationBinary) (a : CalibrationBinary) (B : ℕ)
    (ha : RationalHeight a.value B) (hr : ∀ x∈row,RationalHeight x.value B) (hl : row.length≤2^B) :
    (countedBinaryCDFCounts row a).2≤(row.length+1)*8*calibrationFieldWork B := by
  induction row with
  | nil =>
    simp only [countedBinaryCDFCounts,List.length_nil,zero_add,one_mul]
    unfold calibrationFieldWork
    omega
  | cons x row ih =>
    have hL : row.length≤2^B := by simp only [List.length_cons] at hl; omega
    have hTail := ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) hL
    have h := countedRowCDFCounts_height (row.map BinaryRational.value) a.value B (by simpa using hL)
    rw [← countedBinaryCDFCounts_value] at h
    change RationalHeight (countedBinaryCDFCounts row a).1.1.1.value B ∧
      RationalHeight (countedBinaryCDFCounts row a).1.1.2.value B ∧
      RationalHeight (countedBinaryCDFCounts row a).1.2.value B at h
    have hOne : RationalHeight ((1 : CalibrationBinary).value) B := by
      rw [BinaryRational.one_value]
      exact rationalHeight_one.mono (Nat.zero_le _)
    have h1 := BinaryRational.countedOperation_work .add _ 1 B h.1 hOne
    have h2 := BinaryRational.countedOperation_work .add _ 1 B h.2.1 hOne
    have h3 := BinaryRational.countedOperation_work .add _ 1 B h.2.2 hOne
    have hc := countedCalibrationLT_work x a B (hr x List.mem_cons_self) ha
    have hd := countedCalibrationLE_work x a B (hr x List.mem_cons_self) ha
    have he : ((x::row).length+1)*8*calibrationFieldWork B=
        (row.length+1)*8*calibrationFieldWork B+8*calibrationFieldWork B := by
      simp only [List.length_cons]
      ring
    rw [he]
    unfold countedBinaryCDFCounts
    dsimp only
    split_ifs <;> dsimp only <;> unfold calibrationFieldWork at * <;> omega

def countedBinaryRowCDF (row : List CalibrationBinary) (a : CalibrationBinary) :
    (CalibrationBinary × CalibrationBinary) × ℕ :=
  let q := countedBinaryCDFCounts row a
  let p := BinaryRational.countedOperation .div q.1.1.1 q.1.2
  let t := BinaryRational.countedOperation .div q.1.1.2 q.1.2
  ((p.1,t.1),q.2+p.2+t.2+3)

lemma countedBinaryRowCDF_value (row : List CalibrationBinary) (a : CalibrationBinary) :
    ((countedBinaryRowCDF row a).1.1.value,(countedBinaryRowCDF row a).1.2.value) =
      (countedRowCDF (row.map BinaryRational.value) a.value).1 := by
  have h := countedBinaryCDFCounts_value row a
  have h₁ : (countedBinaryCDFCounts row a).1.1.1.value =
      (countedRowCDFCounts (row.map BinaryRational.value) a.value).1.1.1 :=
    congrArg (fun q : (ℚ×ℚ)×ℚ => q.1.1) h
  have h₂ : (countedBinaryCDFCounts row a).1.1.2.value =
      (countedRowCDFCounts (row.map BinaryRational.value) a.value).1.1.2 :=
    congrArg (fun q : (ℚ×ℚ)×ℚ => q.1.2) h
  have h₃ : (countedBinaryCDFCounts row a).1.2.value =
      (countedRowCDFCounts (row.map BinaryRational.value) a.value).1.2 :=
    congrArg (fun q : (ℚ×ℚ)×ℚ => q.2) h
  simp only [countedBinaryRowCDF,countedCalibrationOp_value,rationalCalibrationOp,countedRowCDF,h₁,h₂,h₃]


lemma countedBinaryRowCDF_work (row : List CalibrationBinary) (a : CalibrationBinary) (B : ℕ)
    (ha : RationalHeight a.value B) (hr : ∀ x∈row,RationalHeight x.value B) (hl : row.length≤2^B) :
    (countedBinaryRowCDF row a).2≤(row.length+1)*12*calibrationFieldWork B := by
  have h := countedRowCDFCounts_height (row.map BinaryRational.value) a.value B (by simpa using hl)
  rw [← countedBinaryCDFCounts_value] at h
  change RationalHeight (countedBinaryCDFCounts row a).1.1.1.value B ∧
    RationalHeight (countedBinaryCDFCounts row a).1.1.2.value B ∧
    RationalHeight (countedBinaryCDFCounts row a).1.2.value B at h
  have h₁ := BinaryRational.countedOperation_work .div _ _ B h.1 h.2.2
  have h₂ := BinaryRational.countedOperation_work .div _ _ B h.2.1 h.2.2
  have hR := countedBinaryCDFCounts_work row a B ha hr hl
  dsimp only [countedBinaryRowCDF]
  let W := calibrationFieldWork B
  have hW : 4≤W := by dsimp [W,calibrationFieldWork]; omega
  have hW' : 3600*(B+2)^3≤W := by dsimp [W,calibrationFieldWork]; omega
  have hMono := Nat.mul_le_mul_right W (show 4≤(row.length+1)*4 by omega)
  have e : (row.length+1)*12*W=(row.length+1)*8*W+(row.length+1)*4*W := by ring
  change _≤(row.length+1)*8*W at hR
  change _≤(row.length+1)*12*W
  rw [e]
  omega

def countedBinaryCDFProducts (rows : List (List CalibrationBinary)) (a : CalibrationBinary) :
    (CalibrationBinary × CalibrationBinary) × ℕ :=
  match rows with
  | [] => ((1,1),2)
  | row::rows =>
    let head := countedBinaryRowCDF row a
    let tail := countedBinaryCDFProducts rows a
    let p := BinaryRational.countedOperation .mul head.1.1 tail.1.1
    let q := BinaryRational.countedOperation .mul head.1.2 tail.1.2
    ((p.1,q.1),head.2+tail.2+p.2+q.2+4)

lemma countedBinaryCDFProducts_value (rows : List (List CalibrationBinary)) (a : CalibrationBinary) :
    ((countedBinaryCDFProducts rows a).1.1.value,(countedBinaryCDFProducts rows a).1.2.value) =
      (countedCDFProducts (rows.map (List.map BinaryRational.value)) a.value).1 := by
  induction rows with
  | nil => simp [countedBinaryCDFProducts,countedCDFProducts]
  | cons row rows ih =>
    have h := countedBinaryRowCDF_value row a
    simp only [countedBinaryCDFProducts,countedCalibrationOp_value,rationalCalibrationOp,
      List.map_cons,countedCDFProducts]
    have h₁ : (countedBinaryRowCDF row a).1.1.value=(countedRowCDF (row.map BinaryRational.value) a.value).1.1 :=
      congrArg Prod.fst h
    have h₂ : (countedBinaryRowCDF row a).1.2.value=(countedRowCDF (row.map BinaryRational.value) a.value).1.2 :=
      congrArg Prod.snd h
    have h₃ : (countedBinaryCDFProducts rows a).1.1.value=
        (countedCDFProducts (rows.map (List.map BinaryRational.value)) a.value).1.1 := congrArg Prod.fst ih
    have h₄ : (countedBinaryCDFProducts rows a).1.2.value=
        (countedCDFProducts (rows.map (List.map BinaryRational.value)) a.value).1.2 := congrArg Prod.snd ih
    rw [h₁,h₂,h₃,h₄]


lemma countedBinaryCDFProducts_work (rows : List (List CalibrationBinary)) (a : CalibrationBinary) (B P : ℕ)
    (ha : RationalHeight a.value B) (hr : ∀ x∈rows.flatten,RationalHeight x.value B)
    (hl : ∀ row∈rows,row.length≤2^P) (hP : P≤B) (hSize : (P+P)*rows.length≤B) :
    (countedBinaryCDFProducts rows a).2≤16*(rows.length+rows.flatten.length+1)*calibrationFieldWork B := by
  induction rows with
  | nil =>
    simp only [countedBinaryCDFProducts,List.length_nil,List.flatten_nil,zero_add,mul_one]
    unfold calibrationFieldWork
    omega
  | cons row rows ih =>
    have hLen := hl row List.mem_cons_self
    have htSize : (P+P)*rows.length≤B :=
      (Nat.mul_le_mul_left _ (by simp)).trans hSize
    have ht := ih (fun x hx => hr x (by simp [hx]))
      (fun r hr => hl r (List.mem_cons_of_mem _ hr)) htSize
    have hR := countedBinaryRowCDF_work row a B ha (fun x hx => hr x (by simp [hx]))
      (hLen.trans (Nat.pow_le_pow_right (by decide) hP))
    have hRow := countedRowCDF_height (row.map BinaryRational.value) a.value P (by simpa using hLen)
    have hTail := countedCDFProducts_height (rows.map (List.map BinaryRational.value)) a.value P (by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      simpa using hl u (List.mem_cons_of_mem _ hu))
    rw [← countedBinaryRowCDF_value] at hRow
    rw [← countedBinaryCDFProducts_value,List.length_map] at hTail
    have hBound : P+P≤B := by
      have h := Nat.mul_le_mul_left (P+P) (show 1≤(row::rows).length by simp)
      exact (by simpa only [Nat.mul_one] using h.trans hSize)
    have h₁ := BinaryRational.countedOperation_work .mul
      (countedBinaryRowCDF row a).1.1 (countedBinaryCDFProducts rows a).1.1 B
      (hRow.1.mono hBound) (hTail.1.mono htSize)
    have h₂ := BinaryRational.countedOperation_work .mul
      (countedBinaryRowCDF row a).1.2 (countedBinaryCDFProducts rows a).1.2 B
      (hRow.2.mono hBound) (hTail.2.mono htSize)
    let W := calibrationFieldWork B
    have hW : 4≤W := by dsimp [W,calibrationFieldWork]; omega
    have hOp : 3600*(B+2)^3≤W := by dsimp [W,calibrationFieldWork]; omega
    have hSlack := Nat.mul_le_mul_right W (show 4≤4*(row.length+1) by omega)
    dsimp only [countedBinaryCDFProducts]
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    have he : 16*(rows.length+1+(row.length+rows.flatten.length)+1)*W=
        16*(rows.length+rows.flatten.length+1)*W+(row.length+1)*12*W+4*(row.length+1)*W := by ring
    change _≤16*(rows.length+rows.flatten.length+1)*W at ht
    change _≤(row.length+1)*12*W at hR
    rw [he]
    omega

def countedBinaryEmpiricalAtoms (support : List CalibrationBinary) (rows : List (List CalibrationBinary)) :
    CalibrationBinary × ℕ :=
  match support with
  | [] => (0,1)
  | a::rest =>
    let p := countedBinaryCDFProducts rows a
    let d := BinaryRational.countedOperation .sub p.1.1 p.1.2
    let x := BinaryRational.countedOperation .mul a d.1
    let tail := countedBinaryEmpiricalAtoms rest rows
    let y := BinaryRational.countedOperation .add x.1 tail.1
    (y.1,p.2+d.2+x.2+tail.2+y.2+5)

lemma countedBinaryEmpiricalAtoms_value (support : List CalibrationBinary) (rows : List (List CalibrationBinary)) :
    (countedBinaryEmpiricalAtoms support rows).1.value =
      (countedEmpiricalAtoms (support.map BinaryRational.value) (rows.map (List.map BinaryRational.value))).1 := by
  induction support with
  | nil => simp [countedBinaryEmpiricalAtoms,countedEmpiricalAtoms]
  | cons a l ih =>
    have h := countedBinaryCDFProducts_value rows a
    simp only [countedBinaryEmpiricalAtoms,countedCalibrationOp_value,rationalCalibrationOp,
      List.map_cons,countedEmpiricalAtoms,ih]
    have h₁ : (countedBinaryCDFProducts rows a).1.1.value=
        (countedCDFProducts (rows.map (List.map BinaryRational.value)) a.value).1.1 := congrArg Prod.fst h
    have h₂ : (countedBinaryCDFProducts rows a).1.2.value=
        (countedCDFProducts (rows.map (List.map BinaryRational.value)) a.value).1.2 := congrArg Prod.snd h
    rw [h₁,h₂]

theorem countedBinaryEmpiricalAtoms_work (support : List CalibrationBinary) (rows : List (List CalibrationBinary))
    (B P Y : ℕ) (hP : P≤B) (hY : Y≤B)
    (hr : ∀ x∈rows.flatten,RationalHeight x.value B) (hs : ∀ x∈support,RationalHeight x.value Y)
    (hL : ∀ row∈rows,row.length≤2^P)
    (hProd : (P+P)*rows.length≤B)
    (hAtom : Y+4*P*rows.length+2≤B)
    (hTotal : support.length*(Y+4*P*rows.length+2)≤B) :
    (countedBinaryEmpiricalAtoms support rows).2≤
      1+support.length*(16*(rows.length+rows.flatten.length+1)+8)*calibrationFieldWork B := by
  induction support with
  | nil => simp [countedBinaryEmpiricalAtoms]
  | cons a l ih =>
    let R := Y+4*P*rows.length+2
    have hRest : l.length*R≤B := (Nat.mul_le_mul_right _ (by simp)).trans hTotal
    have hTail := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hRest
    have hRows : ∀ r∈rows.map (List.map BinaryRational.value),r.length≤2^P := by
      intro r hr
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      simpa using hL s hs
    have hSup : ∀ x∈l.map BinaryRational.value,RationalHeight x Y := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hs y (List.mem_cons_of_mem _ hy)
    have ht := countedEmpiricalAtoms_height (l.map BinaryRational.value)
      (rows.map (List.map BinaryRational.value)) P Y hRows hSup
    rw [← countedBinaryEmpiricalAtoms_value,List.length_map,List.length_map] at ht
    have ha := hs a List.mem_cons_self
    have hAtom' := countedEmpiricalAtom_height (rows.map (List.map BinaryRational.value)) a.value P Y hRows ha
    simp only [← countedBinaryCDFProducts_value,List.length_map] at hAtom'
    have hHead := countedBinaryCDFProducts_work rows a B P (ha.mono hY) hr hL hP hProd
    have hProd' := countedCDFProducts_height (rows.map (List.map BinaryRational.value)) a.value P hRows
    rw [← countedBinaryCDFProducts_value,List.length_map] at hProd'
    let p := countedBinaryCDFProducts rows a
    let d := BinaryRational.countedOperation .sub p.1.1 p.1.2
    let x := BinaryRational.countedOperation .mul a d.1
    have hd : RationalHeight d.1.value B := by
      simp only [d,countedCalibrationOp_value,rationalCalibrationOp]
      exact hAtom'.1.mono (by omega)
    have hx : RationalHeight x.1.value B := by
      simp only [x,d,countedCalibrationOp_value,rationalCalibrationOp]
      exact hAtom'.2.mono (by omega)
    have h₁ : d.2≤3600*(B+2)^3 :=
      BinaryRational.countedOperation_work .sub _ _ B (hProd'.1.mono hProd) (hProd'.2.mono hProd)
    have h₂ : x.2≤3600*(B+2)^3 :=
      BinaryRational.countedOperation_work .mul _ _ B (ha.mono hY) hd
    have h₃ := BinaryRational.countedOperation_work .add x.1 (countedBinaryEmpiricalAtoms l rows).1 B
      hx (ht.mono hRest)
    let W := calibrationFieldWork B
    have hW : 4≤W := by dsimp [W,calibrationFieldWork]; omega
    have hOp : 3600*(B+2)^3≤W := by dsimp [W,calibrationFieldWork]; omega
    change p.2+d.2+x.2+(countedBinaryEmpiricalAtoms l rows).2+
      (BinaryRational.countedOperation .add x.1 (countedBinaryEmpiricalAtoms l rows).1).2+5≤_
    change p.2≤16*(rows.length+rows.flatten.length+1)*W at hHead
    change _≤1+l.length*(16*(rows.length+rows.flatten.length+1)+8)*W at hTail
    change _≤1+(l.length+1)*(16*(rows.length+rows.flatten.length+1)+8)*W
    have he : (l.length+1)*(16*(rows.length+rows.flatten.length+1)+8)*W=
        l.length*(16*(rows.length+rows.flatten.length+1)+8)*W+
        16*(rows.length+rows.flatten.length+1)*W+8*W := by ring
    rw [he]
    omega

def countedBinaryEmpiricalMaximum (rows : List (List CalibrationBinary)) : CalibrationBinary × ℕ :=
  let s := countedCalibrationSupport rows
  let a := countedBinaryEmpiricalAtoms s.1 rows
  (a.1,s.2+a.2+1)

theorem countedBinaryEmpiricalMaximum_value (rows : List (List CalibrationBinary)) :
    (countedBinaryEmpiricalMaximum rows).1.value =
      (countedEmpiricalMaximum (rows.map (List.map BinaryRational.value))).1 := by
  simp only [countedBinaryEmpiricalMaximum,countedEmpiricalMaximum,
    countedBinaryEmpiricalAtoms_value,countedCalibrationSupport_value]

lemma countedCalibrationSupport_length (rows : List (List CalibrationBinary)) :
    (countedCalibrationSupport rows).1.length ≤ rows.flatten.length+1 := by
  have h := countedEmpiricalSupport_length (rows.map (List.map BinaryRational.value))
  rw [← countedCalibrationSupport_value,List.length_map,flattenValueMap,List.length_map] at h
  exact h

lemma countedCalibrationSupport_work (rows : List (List CalibrationBinary)) (B : ℕ)
    (h : ∀ x∈rows.flatten,RationalHeight x.value B) :
    (countedCalibrationSupport rows).2 ≤
      1+2*rows.length+2*rows.flatten.length+
      (1+rows.flatten.length*(calibrationComparisonWork B+2))+
      (rows.flatten.length+2)^2*(calibrationComparisonWork B+4)+2 := by
  let f := countedFlattenRows rows
  let p := countedCalibrationFilter (fun a => countedCalibrationLT 0 a) f.1
  have hf := countedFlattenRows_work rows
  have hfv : f.1=rows.flatten := countedFlattenRows_value rows
  have hp := countedCalibrationFilter_work (fun a => countedCalibrationLT 0 a) f.1
    (calibrationComparisonWork B) (fun a ha => countedCalibrationLT_work 0 a B
      (by simpa using rationalHeight_zero.mono (Nat.zero_le B)) (h a (hfv ▸ ha)))
  have hpv : p.1=rows.flatten.filter (fun a => (countedCalibrationLT 0 a).1) := by
    exact (countedCalibrationFilter_value _ _).trans (congrArg (List.filter _) hfv)
  have hpLen : p.1.length≤rows.flatten.length := by rw [hpv]; exact List.length_filter_le _ _
  have hd := countedCalibrationDistinct_work (0::p.1) B (by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · simpa using rationalHeight_zero.mono (Nat.zero_le B)
    · rw [hpv] at ha
      exact h _ (List.mem_of_mem_filter ha))
  have hLen : (0::p.1).length+1≤rows.flatten.length+2 := by
    simp only [List.length_cons]
    omega
  have hd' := hd.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hLen 2))
  have hpW : p.2≤1+rows.flatten.length*(calibrationComparisonWork B+2) := by
    simpa only [←hfv] using hp
  change f.2+p.2+(countedCalibrationDistinct (0::p.1)).2+2≤_
  change f.2≤_ at hf
  omega

/-- The width used by the CDF products and the sum over distinct support atoms. -/
def binaryEmpiricalMaximumWidth (rows entries Y P : ℕ) : ℕ :=
  Y+P+4*P*rows+(entries+2)*(Y+4*P*rows+2)+2

/-- Each support atom visits each stored sample at most twice, and the binary
operations are performed on normalized fractions of the indicated width. -/
def binaryEmpiricalMaximumWork (rows entries Y P : ℕ) : ℕ :=
  let B := binaryEmpiricalMaximumWidth rows entries Y P
  1+2*rows+2*entries+(1+entries*(calibrationComparisonWork B+2))+
    (entries+2)^2*(calibrationComparisonWork B+4)+2+
    (1+(entries+1)*(16*(rows+entries+1)+8)*calibrationFieldWork B)+1

theorem countedBinaryEmpiricalMaximum_work (rows : List (List CalibrationBinary)) (Y P : ℕ)
    (hY : ∀ a∈rows.flatten,RationalHeight a.value Y)
    (hP : ∀ row∈rows,row.length≤2^P) :
    (countedBinaryEmpiricalMaximum rows).2≤
      binaryEmpiricalMaximumWork rows.length rows.flatten.length Y P := by
  let B := binaryEmpiricalMaximumWidth rows.length rows.flatten.length Y P
  have hBY : Y≤B := by dsimp [B,binaryEmpiricalMaximumWidth]; omega
  have hBP : P≤B := by dsimp [B,binaryEmpiricalMaximumWidth]; omega
  have hR : (P+P)*rows.length≤B := by
    dsimp [B,binaryEmpiricalMaximumWidth]
    have h : (P+P)*rows.length≤4*P*rows.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  let s := countedCalibrationSupport rows
  have hsLen : s.1.length≤rows.flatten.length+1 := countedCalibrationSupport_length rows
  have hsHeight : ∀ a∈s.1,RationalHeight a.value Y := by
    intro a ha
    have h := countedEmpiricalSupport_height (rows.map (List.map BinaryRational.value)) Y (by
      rw [flattenValueMap]
      intro a ha
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      exact hY x hx)
    rw [← countedCalibrationSupport_value] at h
    exact h _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  let R := Y+4*P*rows.length+2
  have hProd : (rows.flatten.length+2)*R≤B := by dsimp [R,B,binaryEmpiricalMaximumWidth]; omega
  have hAtom : R≤B :=
    (Nat.le_mul_of_pos_left _ (by omega : 0<rows.flatten.length+2)).trans hProd
  have hTotal : s.1.length*R≤B := (Nat.mul_le_mul_right _ (hsLen.trans (by omega))).trans hProd
  have hsW := countedCalibrationSupport_work rows B (fun a ha => (hY a ha).mono hBY)
  have haW := countedBinaryEmpiricalAtoms_work s.1 rows B P Y hBP hBY
    (fun a ha => (hY a ha).mono hBY) hsHeight hP hR hAtom hTotal
  have hmW := Nat.mul_le_mul_right (16*(rows.length+rows.flatten.length+1)+8) hsLen
  have hmW := Nat.mul_le_mul_right (calibrationFieldWork B) hmW
  change s.2+(countedBinaryEmpiricalAtoms s.1 rows).2+1≤_
  change s.2≤_ at hsW
  unfold binaryEmpiricalMaximumWork
  change _≤1+2*rows.length+2*rows.flatten.length+
    (1+rows.flatten.length*(calibrationComparisonWork B+2))+
    (rows.flatten.length+2)^2*(calibrationComparisonWork B+4)+2+
    (1+(rows.flatten.length+1)*(16*(rows.length+rows.flatten.length+1)+8)*calibrationFieldWork B)+1
  omega

end ProphetSecretary.Statistics.Calibration
