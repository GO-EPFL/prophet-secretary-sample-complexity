import ProphetSecretary.Statistics.BinaryCalibrationSelection

/-!
# Binary threshold rows and validation scans

Each continuation estimate is stored once. Prefix maxima are accumulated
in order, and the first accepting rank determines the duration.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis
open CalibrationBinaryExpr

def binaryRemainingHorizon (s : CalibrationBinary) : CalibrationBinaryExpr :=
  .node .maximum (.atom 0) (.node .minimum (.atom 1) (.node .sub (.atom 1) (.atom s)))

@[simp] lemma binaryRemainingHorizon_value (s : CalibrationBinary) :
    (binaryRemainingHorizon s).evaluate.1.value=max 0 (min 1 (1-s.value)) := by
  simp only [evaluate_value,binaryRemainingHorizon,CalibrationBinaryExpr.value,rationalCalibrationOp,
    BinaryRational.zero_value,BinaryRational.one_value]

lemma binaryRemainingHorizon_leaves (s : CalibrationBinary) (B : ℕ)
    (h : RationalHeight s.value B) : (binaryRemainingHorizon s).leavesFit B := by
  have h0 : RationalHeight (0:CalibrationBinary).value B := by
    rw [BinaryRational.zero_value]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  have h1 : RationalHeight (1:CalibrationBinary).value B := by
    rw [BinaryRational.one_value]
    exact rationalHeight_one.mono (Nat.zero_le _)
  exact ⟨h0,h1,h1,h⟩

def binaryRankThreshold (z s cached : CalibrationBinary) : CalibrationBinaryExpr :=
  .node .maximum (.node .mul (.atom z) (binaryRemainingHorizon s)) (.atom cached)

@[simp] lemma binaryRankThreshold_value (z s cached : CalibrationBinary) :
    (binaryRankThreshold z s cached).evaluate.1.value=
      max (z.value*max 0 (min 1 (1-s.value))) cached.value := by
  simp only [evaluate_value,binaryRankThreshold,binaryRemainingHorizon,CalibrationBinaryExpr.value,
    rationalCalibrationOp,BinaryRational.zero_value,BinaryRational.one_value]

lemma binaryRankThreshold_leaves (z s cached : CalibrationBinary) (B : ℕ)
    (hz : RationalHeight z.value B) (hs : RationalHeight s.value B)
    (hp : RationalHeight cached.value B) : (binaryRankThreshold z s cached).leavesFit B :=
  ⟨⟨hz,binaryRemainingHorizon_leaves s B hs⟩,hp⟩

def countedBinaryRankAccept (fallback : Bool) (z s cached x : CalibrationBinary) : Bool×ℕ :=
  let cap := countedCalibrationEQ x 1
  if fallback || cap.1 then (cap.1,cap.2+2)
  else
    let pos := countedCalibrationLT 0 x
    if !pos.1 then (false,cap.2+pos.2+3)
    else
      let t := (binaryRankThreshold z s cached).evaluate
      let h := countedCalibrationLE t.1 x
      (h.1,cap.2+pos.2+t.2+h.2+5)

lemma countedBinaryRankAccept_value (fallback : Bool) (z s cached x : CalibrationBinary) :
    (countedBinaryRankAccept fallback z s cached x).1=
      if fallback then decide (x.value=1) else
        decide (x.value=1 ∨ (0<x.value ∧ max (z.value*max 0 (min 1 (1-s.value))) cached.value≤x.value)) := by
  have ht := binaryRankThreshold_value z s cached
  rw [evaluate_value] at ht
  cases fallback <;> by_cases hc : x.value=1 <;> by_cases hp : 0<x.value <;>
    simp [countedBinaryRankAccept,BinaryRational.zero_value,BinaryRational.one_value,hc,hp,ht]

def binaryRankAcceptWork (B : ℕ) : ℕ :=
  3*calibrationComparisonWork (11*(B+1))+11*workUnit 11 B+5

lemma countedBinaryRankAccept_work (fallback : Bool) (z s cached x : CalibrationBinary) (B : ℕ)
    (hz : RationalHeight z.value B) (hs : RationalHeight s.value B)
    (hp : RationalHeight cached.value B) (hx : RationalHeight x.value B) :
    (countedBinaryRankAccept fallback z s cached x).2≤binaryRankAcceptWork B := by
  let A := 11*(B+1)
  have hBA : B≤A := by dsimp [A]; omega
  have h0 : RationalHeight (0:CalibrationBinary).value A := by
    rw [BinaryRational.zero_value]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  have h1 : RationalHeight (1:CalibrationBinary).value A := by
    rw [BinaryRational.one_value]
    exact rationalHeight_one.mono (Nat.zero_le _)
  let t := binaryRankThreshold z s cached
  have htH : RationalHeight t.evaluate.1.value A := by
    rw [evaluate_value]
    exact t.value_height B (binaryRankThreshold_leaves z s cached B hz hs hp)
  have htW : t.evaluate.2≤11*workUnit 11 B :=
    t.evaluate_work 11 B (binaryRankThreshold_leaves z s cached B hz hs hp) (by rfl)
  have hcap := countedCalibrationEQ_work x 1 A (hx.mono hBA) h1
  have hpos := countedCalibrationLT_work 0 x A h0 (hx.mono hBA)
  have hle := countedCalibrationLE_work t.evaluate.1 x A htH (hx.mono hBA)
  change (let cap := countedCalibrationEQ x 1
    if fallback || cap.1 then (cap.1,cap.2+2)
    else let pos := countedCalibrationLT 0 x
      if !pos.1 then (false,cap.2+pos.2+3)
      else let h := countedCalibrationLE t.evaluate.1 x
        (h.1,cap.2+pos.2+t.evaluate.2+h.2+5)).2≤
    3*calibrationComparisonWork A+11*workUnit 11 B+5
  dsimp only
  split_ifs <;> omega

/-- The input holds the first estimated coefficient followed by the
remaining estimates in coefficient order. -/
def countedBinaryPrefixTail (x : CalibrationBinary) :
    List (CalibrationBinary×ℕ) → List CalibrationBinary×ℕ
  | [] => ([x],1)
  | a::l =>
    let q := BinaryRational.countedOperation .maximum x a.1
    let p := countedBinaryPrefixTail q.1 l
    (x::p.1,a.2+q.2+p.2+2)

lemma countedBinaryPrefixTail_value (x : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) :
    (countedBinaryPrefixTail x l).1.map BinaryRational.value =
      (l.map (fun q => q.1.value)).scanl max x.value := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [countedBinaryPrefixTail,List.map_cons,List.scanl_cons,ih,
      countedCalibrationOp_value,rationalCalibrationOp]

lemma countedBinaryPrefixTail_work (x : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) (B W : ℕ)
    (hx : RationalHeight x.value B) (h : ∀ a∈l,RationalHeight a.1.value B ∧ a.2≤W) :
    (countedBinaryPrefixTail x l).2≤1+l.length*(W+3600*(B+2)^3+2) := by
  induction l generalizing x with
  | nil => simp [countedBinaryPrefixTail]
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    let q := BinaryRational.countedOperation .maximum x a.1
    have hqH : RationalHeight q.1.value B := by
      simp only [q,countedCalibrationOp_value,rationalCalibrationOp]
      simpa only [max_self] using hx.max ha.1
    have hqW : q.2≤3600*(B+2)^3 :=
      BinaryRational.countedOperation_work .maximum x a.1 B hx ha.1
    have ht := ih q.1 hqH (fun a ha => h a (List.mem_cons_of_mem _ ha))
    change a.2+q.2+(countedBinaryPrefixTail q.1 l).2+2≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- First accepted rank, using only the stored per-rank quantities. -/
def countedBinaryDurationScan {α : Type*} (test : α → Bool×ℕ) (clock : α → CalibrationBinary) :
    List α → CalibrationBinary×ℕ
  | [] => (1,1)
  | a::l =>
    let q := test a
    if q.1 then (clock a,q.2+2)
    else let p := countedBinaryDurationScan test clock l; (p.1,p.2+q.2+2)

lemma countedBinaryDurationScan_value {α : Type*} (test : α → Bool×ℕ) (clock : α → CalibrationBinary)
    (l : List α) :
    (countedBinaryDurationScan test clock l).1.value =
      (l.find? (fun a => (test a).1)).elim 1 (fun a => (clock a).value) := by
  induction l with
  | nil => exact BinaryRational.one_value
  | cons a l ih =>
    cases h : (test a).1 <;> simp [countedBinaryDurationScan,h,ih]

lemma countedBinaryDurationScan_work {α : Type*} (test : α → Bool×ℕ) (clock : α → CalibrationBinary)
    (l : List α) (W : ℕ) (h : ∀ a∈l,(test a).2≤W) :
    (countedBinaryDurationScan test clock l).2≤1+l.length*(W+2) := by
  induction l with
  | nil => simp [countedBinaryDurationScan]
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [countedBinaryDurationScan]
    dsimp only
    split_ifs <;> simp only [List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

variable {n J : ℕ} {PSeed : Type}

def countedBinaryRankPrefixRow (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (p : Equiv.Perm (Fin n)) (s : Fin n → CalibrationBinary)
    (r : PolicyQueryArray n J PSeed) (k : Fin n) : Array CalibrationBinary×ℕ :=
  let A := active.filter (fun i => k<p.symm i)
  let u := (binaryRemainingHorizon (s k)).evaluate
  let call := fun l : ℕ => estimate A u.1 (z l) (r (k,coefficientIndex J l))
  let a := call 0
  let q := countedBinaryPrefixTail a.1 (List.ofFn (fun l : Fin J => call (l.val+1)))
  (q.1.toArray,n+u.2+a.2+q.2+J+4)

lemma countedBinaryRankPrefixRow_value {m : ℕ} (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (estimateQ : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ×ℕ)
    (he : ∀ A u z s,(estimate A u z s).1.value=(estimateQ A u.value z.value s).1)
    (q : Fin n → Fin m → ℚ) (active : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (s : Fin n → CalibrationBinary) (r : PolicyQueryArray n J PSeed) (k : Fin n)
    (ha : active.filter (fun i => k<p.symm i)=rankContinuationSet q p k) :
    (countedBinaryRankPrefixRow z estimate active p s r k).1.map BinaryRational.value =
      (countedRankPrefixRow (fun l => (z l).value) estimateQ q p (fun i => (s i).value) r k).1 := by
  unfold countedBinaryRankPrefixRow countedRankPrefixRow
  dsimp only
  rw [ha,List.map_toArray,countedBinaryPrefixTail_value]
  simp only [he,binaryRemainingHorizon_value,List.map_ofFn,Function.comp_def]

theorem countedBinaryRankPrefixRow_work (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (p : Equiv.Perm (Fin n)) (s : Fin n → CalibrationBinary)
    (r : PolicyQueryArray n J PSeed) (k : Fin n) (B E W : ℕ)
    (hs : RationalHeight (s k).value B)
    (h : ∀ l : ℕ,l≤J →
      let q := estimate (active.filter (fun i => k<p.symm i))
        (binaryRemainingHorizon (s k)).evaluate.1 (z l) (r (k,coefficientIndex J l))
      RationalHeight q.1.value E ∧ q.2≤W) :
    (countedBinaryRankPrefixRow z estimate active p s r k).2≤
      n+7*workUnit 7 B+(J+1)*(W+3600*(E+2)^3+3)+5 := by
  let u := (binaryRemainingHorizon (s k)).evaluate
  let f := fun l : ℕ => estimate (active.filter (fun i => k<p.symm i))
    u.1 (z l) (r (k,coefficientIndex J l))
  let L := List.ofFn (fun l : Fin J => f (l.val+1))
  have hh : ∀ a∈L,RationalHeight a.1.value E ∧ a.2≤W := by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact h (j.val+1) j.isLt
  have hu : u.2≤7*workUnit 7 B :=
    (binaryRemainingHorizon (s k)).evaluate_work 7 B (binaryRemainingHorizon_leaves _ _ hs) (by rfl)
  have h0 : RationalHeight (f 0).1.value E ∧ (f 0).2≤W := h 0 (Nat.zero_le _)
  have hL := countedBinaryPrefixTail_work (f 0).1 L E W h0.1 hh
  have hLen : L.length=J := List.length_ofFn
  rw [hLen] at hL
  change n+u.2+(f 0).2+(countedBinaryPrefixTail (f 0).1 L).2+J+4≤_
  have hExpansion : (J+1)*(W+3600*(E+2)^3+3)=J*(W+3600*(E+2)^3+2)+J+(W+3600*(E+2)^3+3) := by ring
  rw [hExpansion]
  omega

def countedBinaryRankMemoAccept (z : ℕ → CalibrationBinary) (fallback : Bool)
    (rows : Array (Array CalibrationBinary)) (x s : Fin n → CalibrationBinary)
    (p : Equiv.Perm (Fin n)) (j : Fin (J+1)) (k : Fin n) : Bool×ℕ :=
  countedBinaryRankAccept fallback (z j.val) (s k) ((rows[k.val]?.getD #[])[j.val]?.getD 0) (x (p k))

private lemma binaryPrefixRead_value (rows : Array (Array CalibrationBinary)) (k j : ℕ) :
    (((rows[k]?.getD #[])[j]?.getD 0) : CalibrationBinary).value =
      ((((rows.map (Array.map BinaryRational.value))[k]?.getD #[])[j]?.getD 0) : ℚ) := by
  have hh : ((rows.map (Array.map BinaryRational.value))[k]?).getD #[] =
      (rows[k]?.getD #[]).map BinaryRational.value := by
    rw [Array.getElem?_map]
    cases h : rows[k]? <;> simp
  rw [hh,Array.getElem?_map]
  cases (rows[k]?.getD #[])[j]? <;> simp

lemma countedBinaryRankMemoAccept_value (z : ℕ → CalibrationBinary) (fallback : Bool)
    (rows : Array (Array CalibrationBinary)) (x s : Fin n → CalibrationBinary)
    (p : Equiv.Perm (Fin n)) (j : Fin (J+1)) (k : Fin n) :
    (countedBinaryRankMemoAccept z fallback rows x s p j k).1=
      rankMemoAccepts (fun l => (z l).value) fallback (rows.map (Array.map BinaryRational.value))
        (fun i => (x i).value) (fun i => (s i).value) p j k := by
  rw [countedBinaryRankMemoAccept,countedBinaryRankAccept_value,binaryPrefixRead_value]
  rfl

/-- The table is stored once and shared by the duration scans. -/
def countedBinaryRankValidationMemo (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (fallback : Bool) (p : Equiv.Perm (Fin n))
    (x s : Fin n → CalibrationBinary) (r : PolicyQueryArray n J PSeed) : Array CalibrationBinary×ℕ :=
  let tab := if fallback then #[] else Array.ofFn (countedBinaryRankPrefixRow z estimate active p s r)
  let rows := tab.map Prod.fst
  let dur := fun j : Fin (J+1) =>
    countedBinaryDurationScan (countedBinaryRankMemoAccept z fallback rows x s p j) s (List.finRange n)
  ((Array.ofFn dur).map Prod.fst,
    (tab.toList.map (fun v => v.2+1)).sum+(List.ofFn (fun j => (dur j).2+2)).sum+2)

theorem countedBinaryRankValidationMemo_value {m : ℕ} (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (estimateQ : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ×ℕ)
    (he : ∀ A u z s,(estimate A u z s).1.value=(estimateQ A u.value z.value s).1)
    (q : Fin n → Fin m → ℚ) (active : Finset (Fin n)) (fallback : Bool)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → CalibrationBinary) (r : PolicyQueryArray n J PSeed)
    (ha : ∀ k,active.filter (fun i => k<p.symm i)=rankContinuationSet q p k) :
    (countedBinaryRankValidationMemo z estimate active fallback p x s r).1.map BinaryRational.value =
      (countedRankValidationMemo (fun l => (z l).value) estimateQ q fallback p
        (fun i => (x i).value) (fun i => (s i).value) r).1 := by
  let tab := if fallback then #[] else Array.ofFn (countedBinaryRankPrefixRow z estimate active p s r)
  let rows := tab.map Prod.fst
  let tabQ := if fallback then #[] else Array.ofFn
    (countedRankPrefixRow (fun l => (z l).value) estimateQ q p (fun i => (s i).value) r)
  have hh : rows.map (Array.map BinaryRational.value) = tabQ.map Prod.fst := by
    cases fallback <;> simp [tab,rows,tabQ,Array.map_ofFn,Function.comp_def,
      countedBinaryRankPrefixRow_value z estimate estimateQ he q active p s r _ (ha _)]
  unfold countedBinaryRankValidationMemo countedRankValidationMemo
  dsimp only
  change ((Array.ofFn (fun j : Fin (J+1) =>
    countedBinaryDurationScan (countedBinaryRankMemoAccept z fallback rows x s p j) s
      (List.finRange n))).map Prod.fst).map BinaryRational.value = _
  simp only [Array.map_ofFn,Function.comp_def,countedBinaryDurationScan_value,
    countedBinaryRankMemoAccept_value,hh]
  rfl

private lemma listWorkSum (l : List ℕ) (W : ℕ) (h : ∀ a∈l,a≤W) : l.sum≤l.length*W := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem countedBinaryRankValidationMemo_work (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (fallback : Bool) (p : Equiv.Perm (Fin n))
    (x s : Fin n → CalibrationBinary) (r : PolicyQueryArray n J PSeed) (B E W : ℕ)
    (hz : ∀ j : Fin (J+1),RationalHeight (z j.val).value B)
    (hs : ∀ k,RationalHeight (s k).value B) (hx : ∀ k,RationalHeight (x k).value B)
    (hEB : E≤B)
    (h : ∀ k l,l≤J →
      let q := estimate (active.filter (fun i => k<p.symm i))
        (binaryRemainingHorizon (s k)).evaluate.1 (z l) (r (k,coefficientIndex J l))
      RationalHeight q.1.value E ∧ q.2≤W) :
    (countedBinaryRankValidationMemo z estimate active fallback p x s r).2≤
      n*(n+7*workUnit 7 B+(J+1)*(W+3600*(E+2)^3+3)+6)+
      (J+1)*(3+n*(binaryRankAcceptWork B+2))+2 := by
  let P := n+7*workUnit 7 B+(J+1)*(W+3600*(E+2)^3+3)+6
  let row := countedBinaryRankPrefixRow z estimate active p s r
  let tab := if fallback then #[] else Array.ofFn row
  let rows := tab.map Prod.fst
  have hRow (k : Fin n) : (row k).2+1≤P := by
    have hh := countedBinaryRankPrefixRow_work z estimate active p s r k B E W (hs k) (h k)
    change (row k).2≤_ at hh
    unfold P
    omega
  have hTab : (tab.toList.map (fun v => v.2+1)).sum≤n*P := by
    cases fallback
    · have ht := listWorkSum (List.ofFn (fun k : Fin n => (row k).2+1)) P (by
        intro v hv
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hv
        exact hRow k)
      simpa only [tab,Bool.false_eq_true,ite_false,Array.toList_ofFn,List.map_ofFn,
        Function.comp_def,List.length_ofFn] using ht
    · simp [tab]
  have hRead (k : Fin n) (j : Fin (J+1)) :
      RationalHeight (((rows[k.val]?.getD #[])[j.val]?.getD 0) : CalibrationBinary).value B := by
    cases fallback
    · have hr : (rows[k.val]?.getD #[])=(row k).1 := by
        simp [rows,tab,Array.map_ofFn,k.isLt]
      rw [hr]
      let u := (binaryRemainingHorizon (s k)).evaluate
      let f := fun l : ℕ => estimate (active.filter (fun i => k<p.symm i))
        u.1 (z l) (r (k,coefficientIndex J l))
      let L := List.ofFn (fun l : Fin J => f (l.val+1))
      let a := (f 0).1
      change RationalHeight ((((countedBinaryPrefixTail a L).1.toArray)[j.val]?).getD 0).value B
      have hm : ∀ y∈(countedBinaryPrefixTail a L).1,RationalHeight y.value E := by
        have hAux (l : List (CalibrationBinary×ℕ)) (z : CalibrationBinary)
            (hz : RationalHeight z.value E) (hl : ∀ x∈l,RationalHeight x.1.value E) :
            ∀ y∈(countedBinaryPrefixTail z l).1,RationalHeight y.value E := by
          induction l generalizing z with
          | nil => simpa [countedBinaryPrefixTail] using hz
          | cons b l ih =>
            intro y hy
            rcases List.mem_cons.mp hy with rfl|hy
            · exact hz
            · apply ih _ _ _ y hy
              · rw [countedCalibrationOp_value]
                simpa only [rationalCalibrationOp,max_self] using hz.max (hl b List.mem_cons_self)
              · exact fun x hx => hl x (List.mem_cons_of_mem _ hx)
        apply hAux _ _ (h k 0 (Nat.zero_le _)).1
        intro x hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact (h k (i.val+1) i.isLt).1
      cases he : ((countedBinaryPrefixTail a L).1.toArray)[j.val]? with
      | none =>
        rw [Option.getD_none,BinaryRational.zero_value]
        exact rationalHeight_zero.mono (Nat.zero_le _)
      | some y => exact (hm _ (by simpa using Array.mem_of_getElem? he)).mono hEB
    · simp [rows,tab,BinaryRational.zero_value,rationalHeight_zero.mono (Nat.zero_le B)]
  let dur := fun j : Fin (J+1) =>
    countedBinaryDurationScan (countedBinaryRankMemoAccept z fallback rows x s p j) s (List.finRange n)
  have hDur (j : Fin (J+1)) : (dur j).2+2≤3+n*(binaryRankAcceptWork B+2) := by
    have hh := countedBinaryDurationScan_work (countedBinaryRankMemoAccept z fallback rows x s p j) s
      (List.finRange n) (binaryRankAcceptWork B) (fun k _ =>
        countedBinaryRankAccept_work fallback (z j.val) (s k)
          ((rows[k.val]?.getD #[])[j.val]?.getD 0) (x (p k)) B (hz j) (hs k) (hRead k j) (hx (p k)))
    change (dur j).2≤1+(List.finRange n).length*(binaryRankAcceptWork B+2) at hh
    rw [List.length_finRange] at hh
    omega
  have hDurs := listWorkSum (List.ofFn (fun j => (dur j).2+2)) (3+n*(binaryRankAcceptWork B+2)) (by
    intro v hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    exact hDur j)
  rw [List.length_ofFn] at hDurs
  change (tab.toList.map (fun v => v.2+1)).sum+(List.ofFn (fun j => (dur j).2+2)).sum+2 ≤
    n*P+(J+1)*(3+n*(binaryRankAcceptWork B+2))+2
  omega

end ProphetSecretary.Statistics.Calibration
