import ProphetSecretary.Statistics.CalibratedOuter.BinaryDisplay
import ProphetSecretary.Statistics.CalibratedOuter.TrainingHeight

/-!
# Binary cutoff and pilot

The cutoff scans the tagged rows. The pilot stores the retained maxima
and sorts them using counted binary comparisons.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ}

private lemma binaryVector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

private def countedSelectionScan {α : Type*} (pick : α → α → α × ℕ) :
    α → List α → α × ℕ
  | a, [] => (a,1)
  | a, b::l =>
    let p := pick a b
    let q := countedSelectionScan pick p.1 l
    (q.1,p.2+q.2+2)

private lemma countedSelectionScan_value {α β : Type*} [LinearOrder β]
    (view : α → β) (pick : α → α → α × ℕ)
    (hp : ∀ a b, view (pick a b).1 = max (view a) (view b)) (a : α) (l : List α) :
    view (countedSelectionScan pick a l).1 =
      (countedMaximumFrom (view a) (l.map view)).1 := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [countedSelectionScan,countedMaximumFrom,List.map_cons,ih,hp]

private lemma countedSelectionScan_bounds {α : Type*}
    (pick : α → α → α × ℕ) (P : α → Prop) (U : ℕ) (hU : 1≤U)
    (hp : ∀ a b, P a → P b → P (pick a b).1 ∧ (pick a b).2+2≤U)
    (a : α) (l : List α) (ha : P a) (hl : ∀ b∈l, P b) :
    P (countedSelectionScan pick a l).1 ∧
      (countedSelectionScan pick a l).2≤(l.length+1)*U := by
  induction l generalizing a with
  | nil => simpa [countedSelectionScan] using And.intro ha hU
  | cons b l ih =>
    have h := hp a b ha (hl b List.mem_cons_self)
    have hs := ih _ h.1 (fun c hc => hl c (List.mem_cons_of_mem b hc))
    refine ⟨hs.1,?_⟩
    change (pick a b).2+(countedSelectionScan pick (pick a b).1 l).2+2≤(l.length+1+1)*U
    rw [Nat.add_mul (l.length+1) 1,Nat.one_mul]
    omega

private def countedTaggedMax (a b : BinaryTaggedValue) : BinaryTaggedValue × ℕ :=
  let c := countedBinaryTaggedLT a b
  (if c.1 then b else a,c.2+2)

private def countedTaggedMin (a b : BinaryTaggedValue) : BinaryTaggedValue × ℕ :=
  let c := countedBinaryTaggedLT b a
  (if c.1 then b else a,c.2+2)

private def binaryTaggedLex (a : BinaryTaggedValue) : Lex (ℚ × ℚ) :=
  toLex (binaryTaggedValue a)

private lemma countedTaggedMax_value (a b : BinaryTaggedValue) :
    binaryTaggedLex (countedTaggedMax a b).1 = max (binaryTaggedLex a) (binaryTaggedLex b) := by
  have he : (countedBinaryTaggedLT a b).1=true ↔ binaryTaggedLex a<binaryTaggedLex b :=
    countedBinaryTaggedLT_value a b
  by_cases h : (countedBinaryTaggedLT a b).1=true
  · simp [countedTaggedMax,h,max_eq_right (he.mp h).le]
  · simp [countedTaggedMax,h,max_eq_left (le_of_not_gt (mt he.mpr h))]

private lemma countedTaggedMin_value (a b : BinaryTaggedValue) :
    (show (Lex (ℚ × ℚ))ᵒᵈ from binaryTaggedLex (countedTaggedMin a b).1) =
      max (show (Lex (ℚ × ℚ))ᵒᵈ from binaryTaggedLex a) (binaryTaggedLex b) := by
  have he : (countedBinaryTaggedLT b a).1=true ↔ binaryTaggedLex b<binaryTaggedLex a :=
    countedBinaryTaggedLT_value b a
  change binaryTaggedLex (countedTaggedMin a b).1 = min (binaryTaggedLex a) (binaryTaggedLex b)
  by_cases h : (countedBinaryTaggedLT b a).1=true
  · simp [countedTaggedMin,h,min_eq_right (he.mp h).le]
  · simp [countedTaggedMin,h,min_eq_left (le_of_not_gt (mt he.mpr h))]

private def binaryTaggedUnit (B : ℕ) : ℕ := 10220*(B+2)^3

private lemma countedTaggedMax_bounds (B : ℕ) (a b : BinaryTaggedValue)
    (ha : BinaryTaggedHeight B a) (hb : BinaryTaggedHeight B b) :
    BinaryTaggedHeight B (countedTaggedMax a b).1 ∧ (countedTaggedMax a b).2+2≤binaryTaggedUnit B := by
  have hw := countedBinaryTaggedLT_work a b B ha hb
  have h := Nat.one_le_pow 3 (B+2) (by omega)
  unfold countedTaggedMax binaryTaggedUnit
  dsimp only
  exact ⟨by split <;> assumption,by omega⟩

private lemma countedTaggedMin_bounds (B : ℕ) (a b : BinaryTaggedValue)
    (ha : BinaryTaggedHeight B a) (hb : BinaryTaggedHeight B b) :
    BinaryTaggedHeight B (countedTaggedMin a b).1 ∧ (countedTaggedMin a b).2+2≤binaryTaggedUnit B := by
  have hw := countedBinaryTaggedLT_work b a B hb ha
  have h := Nat.one_le_pow 3 (B+2) (by omega)
  unfold countedTaggedMin binaryTaggedUnit
  dsimp only
  exact ⟨by split <;> assumption,by omega⟩

private def countedBinaryTaggedRow (hn : 0<n) (f : Fin n → BinaryTaggedValue) : BinaryTaggedValue × ℕ :=
  let q := countedSelectionScan countedTaggedMax (f ⟨0,hn⟩) (List.ofFn f)
  (q.1,q.2+n+1)

def countedBinaryCutoff (hm : 1≤m) (a : Fin m → Fin n → BinaryTaggedValue) :
    BinaryTaggedValue × ℕ :=
  if hn : 0<n then
    let rows := Vector.ofFn (fun r : Fin m => countedBinaryTaggedRow hn (a r))
    let v := fun r : Fin m => (rows.get r).1
    let q := countedSelectionScan countedTaggedMin (v ⟨0,by omega⟩) (List.ofFn v)
    (q.1,q.2+(∑ r : Fin m, (rows.get r).2)+4*m+4)
  else ((0,0),1)

lemma countedBinaryCutoff_value (hm : 1≤m) (a : Fin m → Fin n → BinaryTaggedValue) :
    binaryTaggedValue (countedBinaryCutoff hm a).1 =
      (countedCutoff hm (fun r i => binaryTaggedValue (a r i))).1 := by
  by_cases hn : 0<n
  · let v := fun r : Fin m => (countedBinaryTaggedRow hn (a r)).1
    have hv (r : Fin m) : binaryTaggedLex (v r) =
        (countedFiniteMaximum (α := Lex (ℚ × ℚ)) hn (fun i => binaryTaggedLex (a r i))).1 := by
      change binaryTaggedLex (countedSelectionScan countedTaggedMax (a r ⟨0,hn⟩) (List.ofFn (a r))).1 = _
      rw [countedSelectionScan_value binaryTaggedLex countedTaggedMax countedTaggedMax_value]
      simp [countedFiniteMaximum,List.map_ofFn,Function.comp_def]
    have he := countedSelectionScan_value
      (β := (Lex (ℚ × ℚ))ᵒᵈ) binaryTaggedLex countedTaggedMin countedTaggedMin_value
      (v ⟨0,by omega⟩) (List.ofFn v)
    simp only [List.map_ofFn,Function.comp_def,hv] at he
    simp only [countedBinaryCutoff,dif_pos hn,countedCutoff,binaryVector_get_ofFn]
    exact congrArg ofLex he
  · simp [countedBinaryCutoff,countedCutoff,hn,binaryTaggedValue,BinaryRational.zero_value]

theorem countedBinaryCutoff_work (hm : 1≤m) (a : Fin m → Fin n → BinaryTaggedValue)
    (B : ℕ) (ha : ∀ r i, BinaryTaggedHeight B (a r i)) :
    (countedBinaryCutoff hm a).2 ≤ 32000*(m+1)*(n+1)*(B+2)^3 := by
  let U := binaryTaggedUnit B
  have hB : 1≤(B+2)^3 := Nat.one_le_pow _ _ (by omega)
  have hU : 1≤U := by dsimp [U,binaryTaggedUnit]; omega
  by_cases hn : 0<n
  · let v := fun r : Fin m => countedBinaryTaggedRow hn (a r)
    have hr (r : Fin m) : BinaryTaggedHeight B (v r).1 ∧ (v r).2≤(n+1)*U+n+1 := by
      have h := countedSelectionScan_bounds countedTaggedMax (BinaryTaggedHeight B) U hU
        (countedTaggedMax_bounds B) (a r ⟨0,hn⟩) (List.ofFn (a r)) (ha r _) (by
          intro b hb
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
          exact ha r i)
      exact ⟨h.1,by simpa only [v,countedBinaryTaggedRow,List.length_ofFn] using
        Nat.add_le_add_right (Nat.add_le_add_right h.2 n) 1⟩
    have hs := countedSelectionScan_bounds countedTaggedMin (BinaryTaggedHeight B) U hU
      (countedTaggedMin_bounds B) (v ⟨0,by omega⟩).1 (List.ofFn (fun r => (v r).1))
      (hr _).1 (by
        intro b hb
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
        exact (hr i).1)
    have hs' : (countedSelectionScan countedTaggedMin (v ⟨0,by omega⟩).1
        (List.ofFn (fun r => (v r).1))).2 ≤ (m+1)*U := by simpa only [List.length_ofFn] using hs.2
    have hsum : (∑ r : Fin m, (v r).2)≤m*((n+1)*U+n+1) := by
      calc
        _ ≤ ∑ _ : Fin m, ((n+1)*U+n+1) := Finset.sum_le_sum fun r _ => (hr r).2
        _ = _ := by simp
    simp only [countedBinaryCutoff,dif_pos hn,binaryVector_get_ofFn]
    change (countedSelectionScan countedTaggedMin (v ⟨0,by omega⟩).1
        (List.ofFn (fun r => (v r).1))).2+(∑ r : Fin m, (v r).2)+4*m+4≤_
    dsimp only [U,binaryTaggedUnit] at hs' hsum
    nlinarith only [hs',hsum,hB,Nat.mul_le_mul_left (m*n) hB,
      Nat.mul_le_mul_left m hB,Nat.mul_le_mul_left n hB]
  · simp only [countedBinaryCutoff,dif_neg hn]
    exact Nat.succ_le_of_lt (by positivity)

private lemma binaryWorkPos (B : ℕ) : 1≤(B+2)^3 := Nat.one_le_pow _ _ (by omega)

private def countedBinaryMax (a b : BinaryRational) : BinaryRational × ℕ :=
  BinaryRational.countedOperation .maximum a b

private lemma countedBinaryMax_value (a b : BinaryRational) :
    (countedBinaryMax a b).1.value = max a.value b.value := by
  unfold countedBinaryMax
  rw [BinaryRational.countedOperation_value]
  exact BinaryRational.max_value _ _

private lemma binaryZero_height (B : ℕ) : RationalHeight (0:BinaryRational).value B := by
  rw [BinaryRational.zero_value]
  exact rationalHeight_zero.mono (Nat.zero_le _)

private lemma countedBinaryMax_bounds (B : ℕ) (a b : BinaryRational)
    (ha : RationalHeight a.value B) (hb : RationalHeight b.value B) :
    RationalHeight (countedBinaryMax a b).1.value B ∧
      (countedBinaryMax a b).2+2≤3610*(B+2)^3 := by
  have h := BinaryRational.countedOperation_work .maximum a b B ha hb
  have hpos := binaryWorkPos B
  refine ⟨?_,by unfold countedBinaryMax; omega⟩
  rw [countedBinaryMax_value]
  exact (max_choice a.value b.value).elim (fun he => he.symm ▸ ha) (fun he => he.symm ▸ hb)

private def countedBinaryRetain (t z : BinaryTaggedValue) : BinaryRational × ℕ :=
  let r := countedBinaryTaggedLT t z
  (if r.1 then z.1 else 0,r.2+2)

private lemma countedBinaryRetain_value (t z : BinaryTaggedValue) :
    (countedBinaryRetain t z).1.value = countedRetention (binaryTaggedValue t) (binaryTaggedValue z) := by
  by_cases h : (countedBinaryTaggedLT t z).1=true
  · simp only [countedBinaryRetain,countedRetention,if_pos h,if_pos ((countedBinaryTaggedLT_value t z).mp h)]
    rfl
  · simp [countedBinaryRetain,countedRetention,h,mt (countedBinaryTaggedLT_value t z).mpr h,
      BinaryRational.zero_value]

def countedBinaryRetainedMaximum (t : BinaryTaggedValue) (a : Fin n → BinaryTaggedValue) :
    BinaryRational × ℕ :=
  let r := Vector.ofFn (fun i => countedBinaryRetain t (a i))
  let q := countedSelectionScan countedBinaryMax 0 (List.ofFn fun i => (r.get i).1)
  (q.1,q.2+(∑ i : Fin n, (r.get i).2)+4*n+2)

lemma countedBinaryRetainedMaximum_value (t : BinaryTaggedValue) (a : Fin n → BinaryTaggedValue) :
    (countedBinaryRetainedMaximum t a).1.value =
      (countedRetainedMaximum (binaryTaggedValue t) (fun i => binaryTaggedValue (a i))).1 := by
  simp only [countedBinaryRetainedMaximum,binaryVector_get_ofFn]
  rw [countedSelectionScan_value BinaryRational.value countedBinaryMax countedBinaryMax_value]
  simp only [List.map_ofFn,Function.comp_def,countedBinaryRetain_value,BinaryRational.zero_value,
    countedRetention,countedRetainedMaximum]

lemma countedBinaryRetainedMaximum_bounds (t : BinaryTaggedValue) (a : Fin n → BinaryTaggedValue)
    (B : ℕ) (ht : BinaryTaggedHeight B t) (ha : ∀ i, BinaryTaggedHeight B (a i)) :
    RationalHeight (countedBinaryRetainedMaximum t a).1.value B ∧
      (countedBinaryRetainedMaximum t a).2≤15000*(n+1)*(B+2)^3 := by
  let v := fun i : Fin n => countedBinaryRetain t (a i)
  have hpos := binaryWorkPos B
  have hv (i : Fin n) : RationalHeight (v i).1.value B ∧ (v i).2≤10220*(B+2)^3 := by
    have hw := countedBinaryTaggedLT_work t (a i) B ht (ha i)
    unfold v countedBinaryRetain
    dsimp only
    exact ⟨by split; exact (ha i).1; exact binaryZero_height B, by omega⟩
  have hs := countedSelectionScan_bounds countedBinaryMax (fun b => RationalHeight b.value B)
    (3610*(B+2)^3) (by omega) (countedBinaryMax_bounds B) 0 (List.ofFn fun i => (v i).1)
    (binaryZero_height B) (by
      intro b hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      exact (hv i).1)
  have hsum : (∑ i : Fin n, (v i).2)≤n*(10220*(B+2)^3) := by
    calc
      _ ≤ ∑ _ : Fin n, 10220*(B+2)^3 := Finset.sum_le_sum fun i _ => (hv i).2
      _ = _ := by simp
  simp only [countedBinaryRetainedMaximum,binaryVector_get_ofFn]
  refine ⟨hs.1,?_⟩
  have hS := hs.2
  simp only [List.length_ofFn] at hS
  change (countedSelectionScan countedBinaryMax 0 (List.ofFn fun i => (v i).1)).2+
    (∑ i : Fin n, (v i).2)+4*n+2≤_
  nlinarith only [hS,hsum,hpos,Nat.mul_le_mul_left n hpos]

private def countedBinaryInsert (a : BinaryRational) : List BinaryRational → List BinaryRational × ℕ
  | [] => ([a],1)
  | b::l =>
    let t := countedBinaryLE b a
    if t.1 then (a::b::l,t.2+3)
    else let q := countedBinaryInsert a l; (b::q.1,t.2+q.2+3)

private lemma countedBinaryInsert_value (a : BinaryRational) (l : List BinaryRational) :
    (countedBinaryInsert a l).1.map BinaryRational.value =
      List.orderedInsert (fun a b : ℚ => b≤a) a.value (l.map BinaryRational.value) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases he : (countedBinaryLE b a).1=true
    · simp [countedBinaryInsert,he,(countedBinaryLE_value b a).mp he]
    · simp [countedBinaryInsert,he,mt (countedBinaryLE_value b a).mpr he,ih]

private lemma countedBinaryInsert_work (a : BinaryRational) (l : List BinaryRational) (B : ℕ)
    (ha : RationalHeight a.value B) (hl : ∀ b∈l, RationalHeight b.value B) :
    (countedBinaryInsert a l).2 ≤ (l.length+1)*(3410*(B+2)^3) := by
  have hp := binaryWorkPos B
  induction l with
  | nil => simp [countedBinaryInsert]; omega
  | cons b l ih =>
    have hw := countedBinaryLE_work b a B (hl b List.mem_cons_self) ha
    have h := ih (fun c hc => hl c (List.mem_cons_of_mem b hc))
    rw [countedBinaryInsert]
    change _≤(l.length+1+1)*(3410*(B+2)^3)
    rw [Nat.add_mul (l.length+1) 1,Nat.one_mul]
    dsimp only
    split <;> dsimp only <;> omega

private def countedBinarySort : List BinaryRational → List BinaryRational × ℕ
  | [] => ([],1)
  | a::l =>
    let q := countedBinarySort l
    let p := countedBinaryInsert a q.1
    (p.1,q.2+p.2+2)

private lemma countedBinarySort_value (l : List BinaryRational) :
    (countedBinarySort l).1.map BinaryRational.value =
      List.insertionSort (fun a b : ℚ => b≤a) (l.map BinaryRational.value) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [countedBinarySort,countedBinaryInsert_value,ih,List.insertionSort_cons]

private lemma countedBinarySort_length (l : List BinaryRational) : (countedBinarySort l).1.length=l.length := by
  simpa using congrArg List.length (countedBinarySort_value l)

private lemma countedBinarySort_work (l : List BinaryRational) (B : ℕ)
    (hl : ∀ b∈l, RationalHeight b.value B) :
    (countedBinarySort l).2 ≤ (l.length+1)^2*(3420*(B+2)^3) := by
  have hp := binaryWorkPos B
  induction l with
  | nil => simp [countedBinarySort]; omega
  | cons a l ih =>
    have hq := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    have h : ∀ b∈(countedBinarySort l).1, RationalHeight b.value B := by
      intro b hb
      have hb' : b.value∈(countedBinarySort l).1.map BinaryRational.value := List.mem_map.mpr ⟨b,hb,rfl⟩
      rw [countedBinarySort_value,List.mem_insertionSort] at hb'
      obtain ⟨c,hc,he⟩ := List.mem_map.mp hb'
      rw [←he]
      exact hl c (List.mem_cons_of_mem a hc)
    have hP := countedBinaryInsert_work a (countedBinarySort l).1 B (hl a List.mem_cons_self) h
    rw [countedBinarySort_length] at hP
    simp only [countedBinarySort,List.length_cons]
    nlinarith only [hq,hP,hp,Nat.zero_le (l.length*(B+2)^3)]

def countedBinaryPilot (hm : 1≤m) (t : BinaryTaggedValue)
    (a : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue) : BinaryRational × ℕ :=
  let r := Vector.ofFn (fun i => countedBinaryRetainedMaximum t (a i))
  let q := countedBinarySort (List.ofFn fun i => (r.get i).1)
  let k := outerPilotRank m-1
  (q.1.get ⟨k,by
    rw [countedBinarySort_length,List.length_ofFn]
    have := outerPilotRank_pos hm
    unfold outerPilotRounds
    omega⟩,q.2+(∑ i : Fin (outerPilotRounds m), (r.get i).2)+8*(outerPilotRounds m+1))

private lemma binaryGet_eq_of_map (l : List BinaryRational) (r : List ℚ)
    (k : ℕ) (hl : k<l.length) (hr : k<r.length) (h : l.map BinaryRational.value=r) :
    (l.get ⟨k,hl⟩).value = r.get ⟨k,hr⟩ := by
  have he := congrArg (fun z : List ℚ => z[k]?) h
  simp only [List.getElem?_map,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,
    Option.map_some,Option.some.injEq] at he
  exact he

lemma countedBinaryPilot_value (hm : 1≤m) (t : BinaryTaggedValue)
    (a : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue) :
    (countedBinaryPilot hm t a).1.value =
      (countedPilot hm (binaryTaggedValue t) (fun r i => binaryTaggedValue (a r i))).1 := by
  unfold countedBinaryPilot countedPilot countedOrderStatistic
  dsimp only
  apply binaryGet_eq_of_map
  simp only [binaryVector_get_ofFn,countedBinarySort_value,countedInsertionSort_value,List.map_ofFn,
    Function.comp_def,countedBinaryRetainedMaximum_value]

theorem countedBinaryPilot_work (hm : 1≤m) (t : BinaryTaggedValue)
    (a : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue) (B : ℕ)
    (ht : BinaryTaggedHeight B t) (ha : ∀ r i, BinaryTaggedHeight B (a r i)) :
    (countedBinaryPilot hm t a).2 ≤ 19000*(outerPilotRounds m+1)^2*(n+1)*(B+2)^3 := by
  let k := outerPilotRounds m
  let v := fun i : Fin k => countedBinaryRetainedMaximum t (a i)
  have hv (i : Fin k) := countedBinaryRetainedMaximum_bounds t (a i) B ht (ha i)
  have hs := countedBinarySort_work (List.ofFn fun i => (v i).1) B (by
    intro b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact (hv i).1)
  rw [List.length_ofFn] at hs
  have hsum : (∑ i : Fin k, (v i).2)≤k*(15000*(n+1)*(B+2)^3) := by
    calc
      _ ≤ ∑ _ : Fin k, 15000*(n+1)*(B+2)^3 := Finset.sum_le_sum fun i _ => (hv i).2
      _ = _ := by simp
  have hp := binaryWorkPos B
  simp only [countedBinaryPilot,binaryVector_get_ofFn]
  change (countedBinarySort (List.ofFn fun i => (v i).1)).2+(∑ i : Fin k, (v i).2)+8*(k+1)≤
    19000*(k+1)^2*(n+1)*(B+2)^3
  nlinarith only [hs,hsum,hp,Nat.mul_le_mul_left k hp,Nat.zero_le (k^2*(B+2)^3),
    Nat.zero_le (k^2*n*(B+2)^3),Nat.zero_le (k*n*(B+2)^3),Nat.zero_le (n*(B+2)^3)]

end ProphetSecretary.Statistics.Calibration
