import ProphetSecretary.Statistics.CalibratedOuter.BinaryTraining

/-!
# Binary outer preparation

The cutoff and pilot are computed once. A nonzero pilot fixes the scale
for the stored display table. Both the table and its online counterpart
use the same binary display program.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {n m : ℕ}

def countedBinaryZeroTest (x : BinaryRational) : Bool × ℕ :=
  let a := countedBinaryLE x 0
  let b := countedBinaryLE 0 x
  (a.1 && b.1,a.2+b.2+3)

lemma countedBinaryZeroTest_value (x : BinaryRational) :
    (countedBinaryZeroTest x).1=true ↔ x.value=0 := by
  simp only [countedBinaryZeroTest,Bool.and_eq_true,countedBinaryLE_value,BinaryRational.zero_value]
  exact le_antisymm_iff.symm

private lemma binaryZeroHeight (B : ℕ) : RationalHeight (0:BinaryRational).value B := by
  rw [BinaryRational.zero_value]
  exact rationalHeight_zero.mono (Nat.zero_le _)

lemma countedBinaryZeroTest_work (x : BinaryRational) (B : ℕ) (hx : RationalHeight x.value B) :
    (countedBinaryZeroTest x).2≤6810*(B+2)^3 := by
  have h₁ := countedBinaryLE_work x 0 B hx (binaryZeroHeight B)
  have h₂ := countedBinaryLE_work 0 x B (binaryZeroHeight B) hx
  have h₃ := Nat.one_le_pow 3 (B+2) (by omega)
  dsimp only [countedBinaryZeroTest]
  omega

def countedBinaryPilotScale (p : BinaryRational) : BinaryRational × ℕ :=
  BinaryRational.countedOperation .mul (BinaryRational.ofRat 1000) p

@[simp] lemma countedBinaryPilotScale_value (p : BinaryRational) :
    (countedBinaryPilotScale p).1.value=1000*p.value := by
  unfold countedBinaryPilotScale
  rw [BinaryRational.countedOperation_value]
  change (BinaryRational.mul (BinaryRational.ofRat 1000) p).value = _
  simp

private lemma binaryThousandHeight : RationalHeight (1000:ℚ) 10 :=
  rationalHeight_natCast 1000 10 (by decide)

lemma countedBinaryPilotScale_height (p : BinaryRational) (B : ℕ) (hp : RationalHeight p.value B) :
    RationalHeight (countedBinaryPilotScale p).1.value (10+B) := by
  rw [countedBinaryPilotScale_value]
  exact binaryThousandHeight.mul hp

lemma countedBinaryPilotScale_work (p : BinaryRational) (B : ℕ) (hp : RationalHeight p.value B) :
    (countedBinaryPilotScale p).2≤3600*(B+12)^3 := by
  exact BinaryRational.countedOperation_work .mul _ _ (B+10)
    (by rw [BinaryRational.ofRat_value]; exact binaryThousandHeight.mono (by omega)) (hp.mono (by omega))

def countedBinaryPilotDisplay (m : ℕ) (p : BinaryRational) (t z : BinaryTaggedValue) :
    BinaryRational × ℕ :=
  let H := countedBinaryPilotScale p
  let q := countedBinaryDisplay m H.1 t z
  (q.1,H.2+q.2+3)

lemma countedBinaryPilotDisplay_value (m : ℕ) (p : BinaryRational) (t z : BinaryTaggedValue) :
    (countedBinaryPilotDisplay m p t z).1.value =
      (countedDisplay m (1000*p.value) (binaryTaggedValue t) (binaryTaggedValue z)).1 := by
  simp only [countedBinaryPilotDisplay,countedBinaryDisplay_value,countedBinaryPilotScale_value]

theorem countedBinaryDisplay_height (m P : ℕ) (H : BinaryRational) (t z : BinaryTaggedValue)
    (hm : m≤2^P) : RationalHeight (countedBinaryDisplay m H t z).1.value (2*P) := by
  rw [countedBinaryDisplay_value]
  let w := min (max 0 (countedRetention (binaryTaggedValue t) (binaryTaggedValue z)/H.value)) 1
  let X := max w.num.natAbs w.den
  have hX : X≤2^X := (Nat.lt_two_pow_self (n := X)).le
  have hw : RationalHeight w X := ⟨(le_max_left _ _).trans hX,(le_max_right _ _).trans hX⟩
  change RationalHeight (countedMeshRound (1:ℚ) m w).1 (2*P)
  simpa only [Nat.zero_add] using
    (countedMeshRound_operands_height (1:ℚ) w m 0 X P rationalHeight_one hw hm).2.2.2

def binaryOuterDisplayBound (m P B : ℕ) : ℕ :=
  52000*(m+1)*(P+(B+(10+B))+2)^3

lemma countedBinaryPilotDisplay_work (m P B : ℕ) (p : BinaryRational) (t z : BinaryTaggedValue)
    (hm : m≤2^P) (hp : RationalHeight p.value B)
    (ht : BinaryTaggedHeight B t) (hz : BinaryTaggedHeight B z) :
    (countedBinaryPilotDisplay m p t z).2≤3600*(B+12)^3+binaryOuterDisplayBound m P B+3 := by
  have h₁ := countedBinaryPilotScale_work p B hp
  have h₂ := countedBinaryDisplay_work m P B (10+B) (countedBinaryPilotScale p).1 t z hm
    (countedBinaryPilotScale_height p B hp) ht hz
  exact Nat.add_le_add_right (Nat.add_le_add h₁ h₂) 3

private lemma binaryVector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

def countedBinaryOuterPrepare (hm : 1≤m) (cut : Fin m → Fin n → BinaryTaggedValue)
    (pilot : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue)
    (inner : Fin (2*m) → Fin n → BinaryTaggedValue) : CountedOuterPreparation BinaryRational n m :=
  let t := countedBinaryCutoff hm cut
  let p := countedBinaryPilot hm t.1 pilot
  let zero := countedBinaryZeroTest p.1
  if zero.1 then ⟨t.1,p.1,fun _ _ => 0,t.2+p.2+zero.2+5⟩
  else
    let H := countedBinaryPilotScale p.1
    let q : Vector (Vector (BinaryRational × ℕ) (2*m)) n :=
      Vector.ofFn fun i => Vector.ofFn fun j => countedBinaryDisplay m H.1 t.1 (inner j i)
    ⟨t.1,p.1,fun i j => ((q.get i).get j).1,t.2+p.2+zero.2+H.2+5+
      ∑ i : Fin n, ∑ j : Fin (2*m), (((q.get i).get j).2+3)⟩

/-- The binary preparation represents the same cutoff, pilot, and
display table on every input, including the zero-pilot branch. -/
theorem countedBinaryOuterPrepare_value (hm : 1≤m) (cut : Fin m → Fin n → BinaryTaggedValue)
    (pilot : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue)
    (inner : Fin (2*m) → Fin n → BinaryTaggedValue) :
    let p := countedBinaryOuterPrepare hm cut pilot inner
    let q := countedOuterPrepare hm (fun r i => binaryTaggedValue (cut r i))
      (fun r i => binaryTaggedValue (pilot r i)) (fun r i => binaryTaggedValue (inner r i))
    binaryTaggedValue p.cutoff=q.cutoff ∧ p.pilot.value=q.pilot ∧
      ∀ i j, (p.displayed i j).value=q.displayed i j := by
  dsimp only
  let t := (countedBinaryCutoff hm cut).1
  let p := (countedBinaryPilot hm t pilot).1
  have ht : binaryTaggedValue t=(countedCutoff hm (fun r i => binaryTaggedValue (cut r i))).1 :=
    countedBinaryCutoff_value hm cut
  have hp : p.value=(countedPilot hm (binaryTaggedValue t) (fun r i => binaryTaggedValue (pilot r i))).1 :=
    countedBinaryPilot_value hm t pilot
  unfold countedBinaryOuterPrepare countedOuterPrepare
  dsimp only
  rw [← ht,← hp]
  change (let a : CountedOuterPreparation BinaryRational n m := if (countedBinaryZeroTest p).1 then _ else _
          let b : CountedOuterPreparation ℚ n m := if p.value=0 then _ else _
          binaryTaggedValue a.cutoff=b.cutoff ∧ a.pilot.value=b.pilot ∧
            ∀ i j, (a.displayed i j).value=b.displayed i j)
  by_cases h : p.value=0
  · simp only [if_pos h,if_pos ((countedBinaryZeroTest_value p).mpr h),BinaryRational.zero_value]
    exact ⟨rfl,rfl,fun _ _ => True.intro⟩
  · simp only [if_neg h,if_neg (mt (countedBinaryZeroTest_value p).mp h),binaryVector_get_ofFn]
    exact ⟨rfl,rfl,fun i j => by rw [countedBinaryDisplay_value,countedBinaryPilotScale_value]⟩

def binaryOuterPreparationBound (n m P B : ℕ) : ℕ :=
  32000*(m+1)*(n+1)*(B+2)^3+
    19000*(outerPilotRounds m+1)^2*(n+1)*(B+2)^3+
    6810*(B+2)^3+3600*(B+12)^3+5+n*(2*m)*(binaryOuterDisplayBound m P B+3)

theorem countedBinaryOuterPrepare_work (hm : 1≤m) (cut : Fin m → Fin n → BinaryTaggedValue)
    (pilot : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue)
    (inner : Fin (2*m) → Fin n → BinaryTaggedValue) (P B : ℕ) (hmP : m≤2^P)
    (hcut : ∀ r i, BinaryTaggedHeight B (cut r i)) (hpilot : ∀ r i, BinaryTaggedHeight B (pilot r i))
    (hinner : ∀ r i, BinaryTaggedHeight B (inner r i)) :
    (countedBinaryOuterPrepare hm cut pilot inner).work≤binaryOuterPreparationBound n m P B := by
  let t := countedBinaryCutoff hm cut
  let p := countedBinaryPilot hm t.1 pilot
  have ht : BinaryTaggedHeight B t.1 := by
    have h := countedCutoff_height hm (fun r i => binaryTaggedValue (cut r i)) B B hcut
    rw [← countedBinaryCutoff_value hm cut] at h
    exact h
  have hp : RationalHeight p.1.value B := by
    dsimp only [p]
    rw [countedBinaryPilot_value]
    exact countedPilot_height hm _ _ B (fun r i => (hpilot r i).1)
  have hT : t.2≤32000*(m+1)*(n+1)*(B+2)^3 := countedBinaryCutoff_work hm cut B hcut
  have hP : p.2≤19000*(outerPilotRounds m+1)^2*(n+1)*(B+2)^3 :=
    countedBinaryPilot_work hm t.1 pilot B ht hpilot
  have hZ := countedBinaryZeroTest_work p.1 B hp
  have hH := countedBinaryPilotScale_work p.1 B hp
  let H := countedBinaryPilotScale p.1
  have hD (i : Fin n) (j : Fin (2*m)) :
      (countedBinaryDisplay m H.1 t.1 (inner j i)).2+3≤binaryOuterDisplayBound m P B+3 :=
    Nat.add_le_add_right (countedBinaryDisplay_work m P B (10+B) H.1 t.1 (inner j i) hmP
      (countedBinaryPilotScale_height p.1 B hp) ht (hinner j i)) 3
  have hsum : (∑ i : Fin n, ∑ j : Fin (2*m), ((countedBinaryDisplay m H.1 t.1 (inner j i)).2+3))≤
      n*(2*m)*(binaryOuterDisplayBound m P B+3) := by
    calc
      _ ≤ ∑ _ : Fin n, ∑ _ : Fin (2*m), (binaryOuterDisplayBound m P B+3) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ => hD i j
      _ = _ := by simp [Nat.mul_assoc]
  unfold countedBinaryOuterPrepare binaryOuterPreparationBound
  dsimp only
  split_ifs
  · change t.2+p.2+(countedBinaryZeroTest p.1).2+5≤_
    omega
  · simp only [binaryVector_get_ofFn]
    change t.2+p.2+(countedBinaryZeroTest p.1).2+H.2+5+
      (∑ i : Fin n, ∑ j : Fin (2*m), ((countedBinaryDisplay m H.1 t.1 (inner j i)).2+3))≤_
    change H.2≤3600*(B+12)^3 at hH
    omega

/-- The guard in the zero-pilot branch uses only the current tagged offer. -/
def countedBinaryPositiveRetention (t z : BinaryTaggedValue) : Bool × ℕ :=
  let keep := countedBinaryTaggedLT t z
  let nonpos := countedBinaryLE z.1 0
  (keep.1 && !nonpos.1,keep.2+nonpos.2+3)

lemma countedBinaryPositiveRetention_value (t z : BinaryTaggedValue) :
    (countedBinaryPositiveRetention t z).1=true ↔
      0<countedRetention (binaryTaggedValue t) (binaryTaggedValue z) := by
  have hp : (countedBinaryLE z.1 0).1≠true ↔ 0<z.1.value := by
    exact (not_congr ((countedBinaryLE_value z.1 0).trans
      (by rw [BinaryRational.zero_value]))).trans not_le
  by_cases h : (countedBinaryTaggedLT t z).1=true
  · simp only [countedBinaryPositiveRetention,h,Bool.true_and,Bool.not_eq_true',
      Bool.eq_false_iff,hp,countedRetention,if_pos ((countedBinaryTaggedLT_value t z).mp h)]
    rfl
  · have he : (countedBinaryTaggedLT t z).1=false := Bool.eq_false_iff.mpr h
    simp only [countedBinaryPositiveRetention,he,Bool.false_and,Bool.false_eq_true,
      countedRetention,if_neg (mt (countedBinaryTaggedLT_value t z).mpr h),lt_self_iff_false]

lemma countedBinaryPositiveRetention_work (t z : BinaryTaggedValue) (B : ℕ)
    (ht : BinaryTaggedHeight B t) (hz : BinaryTaggedHeight B z) :
    (countedBinaryPositiveRetention t z).2≤13620*(B+2)^3 := by
  have h₁ := countedBinaryTaggedLT_work t z B ht hz
  have h₂ := countedBinaryLE_work z.1 0 B hz.1 (binaryZeroHeight B)
  have h₃ := Nat.one_le_pow 3 (B+2) (by omega)
  dsimp only [countedBinaryPositiveRetention]
  omega

theorem countedBinaryOuterPrepare_height (hm : 1≤m) (cut : Fin m → Fin n → BinaryTaggedValue)
    (pilot : Fin (outerPilotRounds m) → Fin n → BinaryTaggedValue)
    (inner : Fin (2*m) → Fin n → BinaryTaggedValue) (P B : ℕ) (hmP : m≤2^P)
    (hcut : ∀ r i, BinaryTaggedHeight B (cut r i)) (hpilot : ∀ r i, BinaryTaggedHeight B (pilot r i)) :
    let q := countedBinaryOuterPrepare hm cut pilot inner
    BinaryTaggedHeight B q.cutoff ∧ RationalHeight q.pilot.value B ∧
      ∀ i j, RationalHeight (q.displayed i j).value (2*P) := by
  dsimp only
  let t := (countedBinaryCutoff hm cut).1
  let p := (countedBinaryPilot hm t pilot).1
  have ht : BinaryTaggedHeight B t := by
    have h := countedCutoff_height hm (fun r i => binaryTaggedValue (cut r i)) B B hcut
    rw [← countedBinaryCutoff_value hm cut] at h
    exact h
  have hp : RationalHeight p.value B := by
    dsimp only [p]
    rw [countedBinaryPilot_value]
    exact countedPilot_height hm _ _ B (fun r i => (hpilot r i).1)
  unfold countedBinaryOuterPrepare
  dsimp only
  split_ifs
  · exact ⟨ht,hp,fun _ _ => binaryZeroHeight _⟩
  · simp only [binaryVector_get_ofFn]
    exact ⟨ht,hp,fun i j => countedBinaryDisplay_height m P _ _ (inner j i) hmP⟩

end ProphetSecretary.Statistics.Calibration
