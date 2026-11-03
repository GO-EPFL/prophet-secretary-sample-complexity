import ProphetSecretary.Statistics.CalibratedOuter.BinaryOnline
import ProphetSecretary.Statistics.CalibratedOuter.NativeLearner
import ProphetSecretary.Statistics.BinaryFairWords

/-!
# Combining the counted binary outer stages

The marked cutoff, pilot and display are executed with encoded rational
operations. When the pilot is positive, the bounded preparation runs once
on the displayed blocks. The online step retains the rank labels of the
observed history and uses the prepared bounded state.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ} {I : Type*}

structure BinaryOuterStage (n m : ℕ) (I : Type*) where
  transform : CountedOuterPreparation BinaryRational n m
  tags : Fin n → BinaryRational
  inner : Option I
  work : ℕ

def countedBinaryOuterStage (hm : 1≤m) (o : ℕ)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (bits : OuterMarkArray n m (Fin o → Bool))
    (prepare : (Fin n → Fin (2*m) → BinaryRational) → I × ℕ) :
    BinaryOuterStage n m I :=
  let marks := countedCanonicalFairWords o bits
  let tags := unpackOuterMarks marks.1
  let rows := outerRawBlocks y
  let out := countedBinaryOuterPrepare hm (fun r i => (rows.1 i r,tags.1 r i))
    (fun r i => (rows.2.1 i r,tags.2.1 r i)) (fun r i => (rows.2.2 i r,tags.2.2.1 r i))
  let test := countedBinaryZeroTest out.pilot
  if test.1 then ⟨out,tags.2.2.2,none,marks.2+out.work+test.2+4⟩
  else let p := prepare out.displayed
       ⟨out,tags.2.2.2,some p.1,marks.2+out.work+test.2+p.2+4⟩

def binaryOuterStageWorkBound (n m o P B W : ℕ) : ℕ :=
  outerMarkSlotCount n m*(110*(o+2)^3+3)+2+
    binaryOuterPreparationBound n m P B+6810*(B+2)^3+W+4

theorem countedBinaryOuterStage_work (hm : 1≤m) (o P B : ℕ) (hmP : m≤2^P)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (bits : OuterMarkArray n m (Fin o → Bool))
    (hY : ∀ i j, RationalHeight (y i j).value B) (hMarks : o≤B)
    (prepare : (Fin n → Fin (2*m) → BinaryRational) → I × ℕ) (W : ℕ)
    (hPrepare : ∀ q, (∀ i j, RationalHeight (q i j).value (2*P)) → (prepare q).2≤W) :
    (countedBinaryOuterStage hm o y bits prepare).work≤binaryOuterStageWorkBound n m o P B W := by
  let d := countedCanonicalFairWords o bits
  let tags := unpackOuterMarks d.1
  let rows := outerRawBlocks y
  let cut := fun r i => (rows.1 i r,tags.1 r i)
  let pilot := fun r i => (rows.2.1 i r,tags.2.1 r i)
  let inner := fun r i => (rows.2.2 i r,tags.2.2.1 r i)
  let out := countedBinaryOuterPrepare hm cut pilot inner
  have hT (j : Fin (outerMarkSlotCount n m)) : RationalHeight (d.1 j).value B := by
    rw [countedCanonicalFairWords_value,← countedCanonicalFairWord_value]
    exact (countedCanonicalFairWord_height o (bits j)).mono hMarks
  have hc (r) (i) : BinaryTaggedHeight B (cut r i) := ⟨hY _ _,hT _⟩
  have hp (r) (i) : BinaryTaggedHeight B (pilot r i) := ⟨hY _ _,hT _⟩
  have hi (r) (i) : BinaryTaggedHeight B (inner r i) := ⟨hY _ _,hT _⟩
  have hOuter : out.work≤binaryOuterPreparationBound n m P B :=
    countedBinaryOuterPrepare_work hm cut pilot inner P B hmP hc hp hi
  have hHeight := countedBinaryOuterPrepare_height hm cut pilot inner P B hmP hc hp
  dsimp only at hHeight
  have hD : d.2≤outerMarkSlotCount n m*(110*(o+2)^3+3)+2 := countedCanonicalFairWords_work o bits
  have hZero := countedBinaryZeroTest_work out.pilot B hHeight.2.1
  have hInner := hPrepare out.displayed hHeight.2.2
  unfold countedBinaryOuterStage binaryOuterStageWorkBound
  dsimp only
  split_ifs
  · change d.2+out.work+(countedBinaryZeroTest out.pilot).2+4≤_
    omega
  · change d.2+out.work+(countedBinaryZeroTest out.pilot).2+(prepare out.displayed).2+4≤_
    omega

def decideBinaryOuterStage {Time : Type*} (p : BinaryOuterStage n m I)
    (decideInner : I → Time → Fin n → BinaryRational → BinaryOuterHistory n Time → Bool × ℕ)
    (t : Time) (i : Fin n) (x : BinaryRational) (hist : BinaryOuterHistory n Time) : Bool × ℕ :=
  countedBinaryOuterOnline p.transform p.tags
    (fun s j y H => p.inner.elim (false,0) (fun r => decideInner r s j y H)) t i x hist

theorem decideBinaryOuterStage_work {Time : Type*} (hm : 1≤m) (o P B : ℕ) (hmP : m≤2^P)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (bits : OuterMarkArray n m (Fin o → Bool)) (hY : ∀ i j, RationalHeight (y i j).value B)
    (hMarks : o≤B) (prepare : (Fin n → Fin (2*m) → BinaryRational) → I × ℕ)
    (decideInner : I → Time → Fin n → BinaryRational → BinaryOuterHistory n Time → Bool × ℕ)
    (t : Time) (i : Fin n) (x : BinaryRational) (hist : BinaryOuterHistory n Time) (W : ℕ)
    (hx : RationalHeight x.value B)
    (hHist : ∀ j s v, hist j=some (s,v) → RationalHeight v.value B)
    (hInner : ∀ q, (∀ i j, RationalHeight (q i j).value (2*P)) → ∀ y H,
      RationalHeight y.value (2*P) → (∀ j s v, H j=some (s,v) → RationalHeight v.value (2*P)) →
      (decideInner (prepare q).1 t i y H).2≤W) :
    (decideBinaryOuterStage (countedBinaryOuterStage hm o y bits prepare) decideInner t i x hist).2≤
      W+binaryOuterOnlineOverhead n m P B := by
  let d := countedCanonicalFairWords o bits
  let tags := unpackOuterMarks d.1
  let rows := outerRawBlocks y
  let cut := fun r i => (rows.1 i r,tags.1 r i)
  let pilot := fun r i => (rows.2.1 i r,tags.2.1 r i)
  let inner := fun r i => (rows.2.2 i r,tags.2.2.1 r i)
  let out := countedBinaryOuterPrepare hm cut pilot inner
  have hT (j : Fin (outerMarkSlotCount n m)) : RationalHeight (d.1 j).value B := by
    rw [countedCanonicalFairWords_value,← countedCanonicalFairWord_value]
    exact (countedCanonicalFairWord_height o (bits j)).mono hMarks
  have hc (r) (i) : BinaryTaggedHeight B (cut r i) := ⟨hY _ _,hT _⟩
  have hp (r) (i) : BinaryTaggedHeight B (pilot r i) := ⟨hY _ _,hT _⟩
  have hi (r) (i) : BinaryTaggedHeight B (inner r i) := ⟨hY _ _,hT _⟩
  have hHeight := countedBinaryOuterPrepare_height hm cut pilot inner P B hmP hc hp
  dsimp only at hHeight
  unfold decideBinaryOuterStage countedBinaryOuterStage
  dsimp only
  split_ifs
  · apply countedBinaryOuterOnline_work _ _ _ _ _ _ _ P B W hmP hHeight.2.1 hHeight.1
      (fun j => hT _) hx hHist
    intro _ _ _ _ _
    exact Nat.zero_le _
  · apply countedBinaryOuterOnline_work _ _ _ _ _ _ _ P B W hmP hHeight.2.1 hHeight.1
      (fun j => hT _) hx hHist
    intro v H _ hv hH
    exact hInner out.displayed hHeight.2.2 v H hv hH

private def binaryMarksValue (t : OuterMarks n m BinaryRational) : OuterMarks n m ℚ :=
  (fun r i => (t.1 r i).value,fun r i => (t.2.1 r i).value,
    fun r i => (t.2.2.1 r i).value,fun i => (t.2.2.2 i).value)

private lemma binaryMarksValue_eq (o : ℕ) (bits : OuterMarkArray n m (Fin o → Bool)) :
    binaryMarksValue (unpackOuterMarks (countedCanonicalFairWords o bits).1) =
      (countedFiniteOuterMarks o bits).1 := by
  have h : (fun j => ((countedCanonicalFairWords o bits).1 j).value) =
      fun j => (countedStoredDyadicUniform o (bits j)).1 := by
    funext j
    simp only [countedCanonicalFairWords_value,countedStoredDyadicUniform_value,
      countedDyadicUniform,countedFairBitsIndex_value]
  have hMap : binaryMarksValue (unpackOuterMarks (countedCanonicalFairWords o bits).1) =
      unpackOuterMarks (fun j => ((countedCanonicalFairWords o bits).1 j).value) := rfl
  rw [hMap,h]
  unfold countedFiniteOuterMarks
  dsimp only
  apply congrArg unpackOuterMarks
  funext j
  have he : (Vector.ofFn (fun i : Fin (outerMarkSlotCount n m) =>
      countedStoredDyadicUniform o (bits i))).get j=countedStoredDyadicUniform o (bits j) :=
    Vector.getElem_ofFn j.isLt
  exact congrArg Prod.fst he.symm

/-- The binary outer stages realize the native rational outer stages once
the bounded binary callback is identified on the displayed sample block. -/
theorem decideBinaryOuterStage_value_of_inner {J : ℕ} (hm : 1≤m) (T P : FairCallSchedule)
    (b c o : ℕ) (mu zlo zhi Lbar : ℚ)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (bits : OuterMarkArray n m (Fin o → Bool))
    (seeds : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (prepare : (Fin n → Fin (2*m) → BinaryRational) → I × ℕ)
    (decideInner : I → Fin n → Fin n → BinaryRational → BinaryOuterHistory n (Fin n) → Bool × ℕ)
    (k i : Fin n) (x : BinaryRational) (hist : BinaryOuterHistory n (Fin n))
    (hInner : ∀ d v H, onlineQueryRank H i=onlineQueryRank hist i →
      (decideInner (prepare d).1 k i v H).1=
      (countedFiniteCalibrationDecision P zlo zhi
        (countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
          (fun j l => (d j (finiteTrainingIndex m l)).value)
          (fun l j => (d j (finiteValidationIndex m l)).value) seeds)
        i v.value (binaryOuterHistoryValue H)).1) :
    let rows := outerRawBlocks (fun i j => (y i j).value)
    let q := countedFiniteOuterPrepare hm T P b c o mu zlo zhi Lbar
      (fun r i => rows.1 i r) (fun r i => rows.2.1 i r) (fun r i => rows.2.2 i r) bits seeds
    (decideBinaryOuterStage (countedBinaryOuterStage hm o y bits prepare) decideInner k i x hist).1 =
      (countedFiniteOuterDecision P zlo zhi q k i x.value (binaryOuterHistoryValue hist)).1 := by
  dsimp only
  let d := countedCanonicalFairWords o bits
  let tags := unpackOuterMarks d.1
  let t := (countedFiniteOuterMarks o bits).1
  let rows := outerRawBlocks y
  let cut := fun r i => (rows.1 i r,tags.1 r i)
  let pilot := fun r i => (rows.2.1 i r,tags.2.1 r i)
  let inner := fun r i => (rows.2.2 i r,tags.2.2.1 r i)
  let out := countedBinaryOuterPrepare hm cut pilot inner
  let R := outerRawBlocks (fun i j => (y i j).value)
  let q := countedOuterPrepare hm (fun r i => (R.1 i r,t.1 r i))
    (fun r i => (R.2.1 i r,t.2.1 r i)) (fun r i => (R.2.2 i r,t.2.2.1 r i))
  have hTags : binaryMarksValue tags=t := binaryMarksValue_eq o bits
  have hQ : q=countedOuterPrepare hm (fun r i => binaryTaggedValue (cut r i))
      (fun r i => binaryTaggedValue (pilot r i)) (fun r i => binaryTaggedValue (inner r i)) := by
    unfold q
    rw [← hTags]
    rfl
  have hV := countedBinaryOuterPrepare_value hm cut pilot inner
  dsimp only at hV
  have hc : binaryTaggedValue out.cutoff=q.cutoff := hV.1.trans (congrArg _ hQ).symm
  have hp : out.pilot.value=q.pilot := hV.2.1.trans (congrArg _ hQ).symm
  have hD : (fun j l => (out.displayed j l).value)=q.displayed :=
    (funext fun j => funext fun l => hV.2.2 j l).trans (congrArg _ hQ).symm
  have ht : (fun j => (tags.2.2.2 j).value)=t.2.2.2 := congrArg (fun u : OuterMarks n m ℚ => u.2.2.2) hTags
  have hBcut : (binaryOuterPreparationValue out).cutoff=q.cutoff := hc
  have hBpilot : (binaryOuterPreparationValue out).pilot=q.pilot := hp
  unfold decideBinaryOuterStage countedBinaryOuterStage countedFiniteOuterPrepare
  dsimp only
  by_cases h0 : q.pilot=0
  · have hZ : (countedBinaryZeroTest out.pilot).1=true :=
      (countedBinaryZeroTest_value out.pilot).mpr (hp.trans h0)
    rw [if_pos hZ,if_pos h0]
    let F : Fin n → Fin n → BinaryRational → BinaryOuterHistory n (Fin n) → Bool × ℕ := fun _ _ _ _ => (false,0)
    let G : Fin n → Fin n → ℚ → (Fin n → Option (Fin n × ℚ)) → Bool × ℕ := fun _ _ _ _ => (false,1)
    change (countedBinaryOuterOnline out tags.2.2.2 F k i x hist).1 =
      (countedOuterOnline q t.2.2.2 G k i x.value (binaryOuterHistoryValue hist)).1
    rw [countedBinaryOuterOnline_value out tags.2.2.2 F G k i x hist (fun _ _ _ => rfl)]
    rw [ht]
    simp only [countedOuterOnline,hBcut,hBpilot,if_pos h0]
  · have hZ : (countedBinaryZeroTest out.pilot).1≠true :=
      fun h => h0 (hp.symm.trans ((countedBinaryZeroTest_value out.pilot).mp h))
    rw [if_neg hZ,if_neg h0]
    let Q := countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
      (fun i j => q.displayed i (finiteTrainingIndex m j))
      (fun j i => q.displayed i (finiteValidationIndex m j)) seeds
    let F := fun t j y H => decideInner (prepare out.displayed).1 t j y H
    let G := fun (_ j : Fin n) (y : ℚ) (H : Fin n → Option (Fin n × ℚ)) =>
      countedFiniteCalibrationDecision P zlo zhi Q j y H
    have he (v H) (h : onlineQueryRank H i=onlineQueryRank hist i) :
        (F k i v H).1=(G k i v.value (binaryOuterHistoryValue H)).1 := by
      have he := hInner out.displayed v H h
      change (F k i v H).1=_
      unfold G Q
      exact he.trans (by
        have h1 : (fun j l => (out.displayed j (finiteTrainingIndex m l)).value) =
            fun j l => q.displayed j (finiteTrainingIndex m l) := by rw [← hD]
        have h2 : (fun l j => (out.displayed j (finiteValidationIndex m l)).value) =
            fun l j => q.displayed j (finiteValidationIndex m l) := by rw [← hD]
        rw [h1,h2])
    change (countedBinaryOuterOnline out tags.2.2.2 F k i x hist).1 =
      (countedOuterOnline q t.2.2.2 G k i x.value (binaryOuterHistoryValue hist)).1
    rw [countedBinaryOuterOnline_value out tags.2.2.2 F G k i x hist he]
    rw [ht]
    simp only [countedOuterOnline,hBcut,hBpilot,if_neg h0]

end ProphetSecretary.Statistics.Calibration
