import ProphetSecretary.Statistics.CalibratedOuter.BinaryPreparation
import ProphetSecretary.Statistics.CalibratedOuter.Work
import ProphetSecretary.Statistics.CountedOnlineCalibration

/-!
# Binary online display

Each history entry retains its identity, presence flag, and arrival label.
Only the observed values are transformed. The inner decision receives the
current displayed value and the displayed history.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {n m : ℕ} {T : Type*}

private lemma binaryVector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

abbrev BinaryOuterHistory (n : ℕ) (T : Type*) := Fin n → Option (T × BinaryRational)

def binaryOuterHistoryValue (h : BinaryOuterHistory n T) : Fin n → Option (T × ℚ) :=
  fun i => (h i).map (fun p => (p.1,p.2.value))

def countedBinaryOuterHistory (m : ℕ) (H : BinaryRational) (cutoff : BinaryTaggedValue)
    (tags : Fin n → BinaryRational) (hist : BinaryOuterHistory n T) :
    BinaryOuterHistory n T × ℕ :=
  let a := Vector.ofFn fun i =>
    match hist i with
    | none => (none,2)
    | some (t,x) =>
      let d := countedBinaryDisplay m H cutoff (x,tags i)
      (some (t,d.1),d.2+6)
  (fun i => (a.get i).1,(∑ i : Fin n, (a.get i).2)+3)

lemma countedBinaryOuterHistory_value (m : ℕ) (H : BinaryRational) (cutoff : BinaryTaggedValue)
    (tags : Fin n → BinaryRational) (hist : BinaryOuterHistory n T) :
    binaryOuterHistoryValue (countedBinaryOuterHistory m H cutoff tags hist).1 =
      (countedOuterHistory m H.value (binaryTaggedValue cutoff) (fun j => (tags j).value)
        (binaryOuterHistoryValue hist)).1 := by
  funext j
  simp only [countedBinaryOuterHistory,countedOuterHistory,binaryVector_get_ofFn,binaryOuterHistoryValue]
  cases h : hist j with
  | none => rfl
  | some p =>
    obtain ⟨t,x⟩ := p
    simp only [Option.map_some,countedBinaryDisplay_value,binaryTaggedValue]

lemma countedBinaryOuterHistory_isSome (m : ℕ) (H : BinaryRational) (cutoff : BinaryTaggedValue)
    (tags : Fin n → BinaryRational) (hist : BinaryOuterHistory n T) (j : Fin n) :
    ((countedBinaryOuterHistory m H cutoff tags hist).1 j).isSome = (hist j).isSome := by
  simp only [countedBinaryOuterHistory,binaryVector_get_ofFn]
  cases hist j <;> rfl

lemma countedBinaryOuterHistory_rank (m : ℕ) (H : BinaryRational) (cutoff : BinaryTaggedValue)
    (tags : Fin n → BinaryRational) (hist : BinaryOuterHistory n T) (i : Fin n) :
    onlineQueryRank (countedBinaryOuterHistory m H cutoff tags hist).1 i=onlineQueryRank hist i := by
  unfold onlineQueryRank
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,countedBinaryOuterHistory_isSome]

lemma countedBinaryOuterHistory_height (m P : ℕ) (H : BinaryRational) (cutoff : BinaryTaggedValue)
    (tags : Fin n → BinaryRational) (hist : BinaryOuterHistory n T) (hm : m≤2^P) :
    ∀ i t y, (countedBinaryOuterHistory m H cutoff tags hist).1 i=some (t,y) →
      RationalHeight y.value (2*P) := by
  intro i t y h
  simp only [countedBinaryOuterHistory,binaryVector_get_ofFn] at h
  cases he : hist i with
  | none => simp [he] at h
  | some p =>
    obtain ⟨s,x⟩ := p
    simp only [he,Option.some.injEq,Prod.mk.injEq] at h
    rw [←h.2]
    exact countedBinaryDisplay_height m P H cutoff (x,tags i) hm

lemma countedBinaryOuterHistory_work (m P B X : ℕ) (H : BinaryRational) (cutoff : BinaryTaggedValue)
    (tags : Fin n → BinaryRational) (hist : BinaryOuterHistory n T)
    (hm : m≤2^P) (hH : RationalHeight H.value X) (hc : BinaryTaggedHeight B cutoff)
    (hTag : ∀ i, RationalHeight (tags i).value B)
    (hHist : ∀ i t x, hist i=some (t,x) → RationalHeight x.value B) :
    (countedBinaryOuterHistory m H cutoff tags hist).2≤n*(52000*(m+1)*(P+(B+X)+2)^3+6)+3 := by
  simp only [countedBinaryOuterHistory,binaryVector_get_ofFn]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _ : Fin n, (52000*(m+1)*(P+(B+X)+2)^3+6) := by
      apply Finset.sum_le_sum
      intro i _
      cases he : hist i with
      | none => simp only; omega
      | some p =>
        obtain ⟨t,x⟩ := p
        exact Nat.add_le_add_right
          (countedBinaryDisplay_work m P B X H cutoff (x,tags i) hm hH hc ⟨hHist i t x he,hTag i⟩) 6
    _ = _ := by simp

def binaryOuterPreparationValue (q : CountedOuterPreparation BinaryRational n m) :
    CountedOuterPreparation ℚ n m :=
  ⟨binaryTaggedValue q.cutoff,q.pilot.value,fun i j => (q.displayed i j).value,q.work⟩

def countedBinaryOuterOnline (q : CountedOuterPreparation BinaryRational n m) (tags : Fin n → BinaryRational)
    (inner : T → Fin n → BinaryRational → BinaryOuterHistory n T → Bool × ℕ)
    (t : T) (i : Fin n) (x : BinaryRational) (hist : BinaryOuterHistory n T) : Bool × ℕ :=
  let zero := countedBinaryZeroTest q.pilot
  if zero.1 then
    let p := countedBinaryPositiveRetention q.cutoff (x,tags i)
    (p.1,zero.2+p.2+3)
  else
    let H := countedBinaryPilotScale q.pilot
    let a := countedBinaryDisplay m H.1 q.cutoff (x,tags i)
    let h := countedBinaryOuterHistory m H.1 q.cutoff tags hist
    let out := inner t i a.1 h.1
    (out.1,zero.2+H.2+a.2+h.2+out.2+6)

/-- The callback contract may depend on the prefix rank. The binary
history transformation preserves the presence flag of every identity. -/
theorem countedBinaryOuterOnline_value (q : CountedOuterPreparation BinaryRational n m)
    (tags : Fin n → BinaryRational)
    (inner : T → Fin n → BinaryRational → BinaryOuterHistory n T → Bool × ℕ)
    (ref : T → Fin n → ℚ → (Fin n → Option (T × ℚ)) → Bool × ℕ)
    (t : T) (i : Fin n) (x : BinaryRational) (hist : BinaryOuterHistory n T)
    (hInner : ∀ y h, onlineQueryRank h i=onlineQueryRank hist i →
      (inner t i y h).1 = (ref t i y.value (binaryOuterHistoryValue h)).1) :
    (countedBinaryOuterOnline q tags inner t i x hist).1 =
      (countedOuterOnline (binaryOuterPreparationValue q) (fun j => (tags j).value)
        ref t i x.value (binaryOuterHistoryValue hist)).1 := by
  have he := countedBinaryZeroTest_value q.pilot
  unfold countedBinaryOuterOnline countedOuterOnline binaryOuterPreparationValue
  dsimp only
  by_cases hp : q.pilot.value=0
  · simp only [if_pos hp,if_pos (he.mpr hp)]
    apply Bool.eq_iff_iff.mpr
    rw [countedBinaryPositiveRetention_value,decide_eq_true_eq]
    rfl
  · simp only [if_neg hp,if_neg (mt he.mp hp)]
    let H := (countedBinaryPilotScale q.pilot).1
    let a := (countedBinaryDisplay m H q.cutoff (x,tags i)).1
    let h := (countedBinaryOuterHistory m H q.cutoff tags hist).1
    have hEq := hInner a h (countedBinaryOuterHistory_rank m H q.cutoff tags hist i)
    rw [countedBinaryOuterHistory_value,countedBinaryPilotScale_value] at hEq
    rw [show a.value=(countedDisplay m (1000*q.pilot.value) (binaryTaggedValue q.cutoff)
      (x.value,(tags i).value)).1 by
        dsimp only [a,H]
        rw [countedBinaryDisplay_value,countedBinaryPilotScale_value]
        rfl] at hEq
    exact hEq

def binaryOuterOnlineOverhead (n m P B : ℕ) : ℕ :=
  20430*(B+2)^3+3600*(B+12)^3+(n+1)*(binaryOuterDisplayBound m P B+6)+9

theorem countedBinaryOuterOnline_work (q : CountedOuterPreparation BinaryRational n m)
    (tags : Fin n → BinaryRational)
    (inner : T → Fin n → BinaryRational → BinaryOuterHistory n T → Bool × ℕ)
    (t : T) (i : Fin n) (x : BinaryRational) (hist : BinaryOuterHistory n T)
    (P B W : ℕ) (hm : m≤2^P) (hPilot : RationalHeight q.pilot.value B)
    (hCut : BinaryTaggedHeight B q.cutoff) (hTag : ∀ j, RationalHeight (tags j).value B)
    (hx : RationalHeight x.value B)
    (hHist : ∀ j s y, hist j=some (s,y) → RationalHeight y.value B)
    (hInner : ∀ y h, onlineQueryRank h i=onlineQueryRank hist i → RationalHeight y.value (2*P) →
      (∀ j s z, h j=some (s,z) → RationalHeight z.value (2*P)) → (inner t i y h).2≤W) :
    (countedBinaryOuterOnline q tags inner t i x hist).2≤W+binaryOuterOnlineOverhead n m P B := by
  have hZ := countedBinaryZeroTest_work q.pilot B hPilot
  have hR := countedBinaryPositiveRetention_work q.cutoff (x,tags i) B hCut ⟨hx,hTag i⟩
  have hS := countedBinaryPilotScale_work q.pilot B hPilot
  let H := (countedBinaryPilotScale q.pilot).1
  let a := countedBinaryDisplay m H q.cutoff (x,tags i)
  let h := countedBinaryOuterHistory m H q.cutoff tags hist
  have hH : RationalHeight H.value (10+B) := countedBinaryPilotScale_height q.pilot B hPilot
  have hA : a.2≤binaryOuterDisplayBound m P B :=
    countedBinaryDisplay_work m P B (10+B) H q.cutoff (x,tags i) hm hH hCut ⟨hx,hTag i⟩
  have hW : h.2≤n*(binaryOuterDisplayBound m P B+6)+3 :=
    countedBinaryOuterHistory_work m P B (10+B) H q.cutoff tags hist hm hH hCut hTag hHist
  have hI := hInner a.1 h.1 (countedBinaryOuterHistory_rank m H q.cutoff tags hist i)
    (countedBinaryDisplay_height m P H q.cutoff (x,tags i) hm)
    (countedBinaryOuterHistory_height m P H q.cutoff tags hist hm)
  unfold countedBinaryOuterOnline binaryOuterOnlineOverhead
  dsimp only
  split_ifs
  · omega
  · change (countedBinaryZeroTest q.pilot).2+(countedBinaryPilotScale q.pilot).2+a.2+h.2+
      (inner t i a.1 h.1).2+6≤_
    rw [Nat.add_mul (n:ℕ) 1,Nat.one_mul]
    omega

end ProphetSecretary.Statistics.Calibration
