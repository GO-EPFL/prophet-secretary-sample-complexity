import ProphetSecretary.Statistics.CalibratedOuter.BinarySchedule
import ProphetSecretary.Statistics.BinaryBoundedRankExecution

/-!
# The counted binary learner

The outer stage and the bounded calibration each store their preparation.
The online decision reads the current value and past history in encoded
form, retaining the original value for reward. The two cached confidence
levels are public integers.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m J : ℕ}

abbrev BinaryBoundedState (n m J : ℕ) (S : Type) :=
  (Fin n → Fin m → BinaryRational) × BinaryBoundedRankPreparation n m J S

def countedBinaryLearnerPrepare (hm : 1≤m) (T P : FairCallSchedule) (ta pa : ℕ)
    (hta : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hpa : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : BinaryRational) (b c o : ℕ)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (marks : OuterMarkArray n m (Fin o → Bool))
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    BinaryOuterStage n m (BinaryBoundedState n m J (P.Seed n)) :=
  countedBinaryOuterStage hm o y marks (fun d =>
    let rows := fun i j => d i (finiteTrainingIndex m j)
    let validation := fun j i => d i (finiteValidationIndex m j)
    let q := countedBinaryBoundedRankPrepare T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
      rows validation b c bits
    ((rows,q),q.work+2))

def countedBinaryLearnerDecision (P : FairCallSchedule) (pa : ℕ)
    (hpa : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (policyAccuracy : BinaryRational) (q : BinaryOuterStage n m (BinaryBoundedState n m J (P.Seed n)))
    (k i : Fin n) (x : BinaryRational) (H : BinaryOuterHistory n (Fin n)) : Bool × ℕ :=
  decideBinaryOuterStage q (fun p _ i x H =>
    countedBinaryBoundedRankDecision P pa hpa p.1 policyAccuracy p.2 i x H) k i x H

theorem countedBinaryLearnerPrepare_work (hm : 1≤m) (T P : FairCallSchedule) (ta pa : ℕ)
    (hta : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hpa : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : BinaryRational) (b c o : ℕ)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (marks : OuterMarkArray n m (Fin o → Bool))
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (M B D K HT HP : ℕ) (hmM : m≤2^M) (hJ : J≤2^K)
    (hY : ∀ i j, RationalHeight (y i j).value B) (hMarks : o≤B)
    (hmu : RationalHeight mu.value D) (hzlo : RationalHeight zlo.value D) (hzhi : RationalHeight zhi.value D)
    (hT : RationalHeight targetAccuracy.value HT) (hP : RationalHeight policyAccuracy.value HP) :
    (countedBinaryLearnerPrepare hm T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
      b c o y marks bits).work≤
      binaryOuterStageWorkBound n m o M B
        (binaryBoundedRankPrepareWork T P n m J b c (2*M) M D K HT HP+2) := by
  unfold countedBinaryLearnerPrepare
  apply countedBinaryOuterStage_work hm o M B hmM y marks hY hMarks
  intro d hd
  apply Nat.add_le_add_right
  exact countedBinaryBoundedRankPrepare_work T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
    (fun i j => d i (finiteTrainingIndex m j)) (fun j i => d i (finiteValidationIndex m j)) b c bits
    (2*M) M D K HT HP (fun _ _ => hd _ _) (fun _ _ => hd _ _) hmM hJ hmu hzlo hzhi hT hP

theorem countedBinaryLearnerDecision_work (hm : 1≤m) (T P : FairCallSchedule) (ta pa : ℕ)
    (hta : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hpa : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : BinaryRational) (b c o : ℕ)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (marks : OuterMarkArray n m (Fin o → Bool))
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (M B D K HP : ℕ) (hmM : m≤2^M) (hJ : J≤2^K)
    (hY : ∀ i j, RationalHeight (y i j).value B) (hMarks : o≤B)
    (hzlo : RationalHeight zlo.value D) (hzhi : RationalHeight zhi.value D)
    (hP : RationalHeight policyAccuracy.value HP)
    (k i : Fin n) (x : BinaryRational) (H : BinaryOuterHistory n (Fin n))
    (hx : RationalHeight x.value B)
    (hH : ∀ j s v, H j=some (s,v) → RationalHeight v.value B) :
    (countedBinaryLearnerDecision P pa hpa policyAccuracy
      (countedBinaryLearnerPrepare hm T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
        b c o y marks bits) k i x H).2≤
      binaryBoundedRankDecisionWork P n m J b (2*M) M D K HP+binaryOuterOnlineOverhead n m M B := by
  unfold countedBinaryLearnerPrepare countedBinaryLearnerDecision
  apply decideBinaryOuterStage_work hm o M B hmM y marks hY hMarks _ _ k i x H _ hx hH
  intro d hd v H' hv _
  exact countedBinaryBoundedRankDecision_work T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
    (fun i j => d i (finiteTrainingIndex m j)) (fun j i => d i (finiteValidationIndex m j)) b c bits
    i v H' (2*M) M D K HP (fun _ _ => hd _ _) hv hmM hJ hzlo hzhi hP

theorem countedBinaryLearnerDecision_value (hm : 1≤m) (T P : FairCallSchedule) (ta pa : ℕ)
    (hta : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hpa : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : BinaryRational)
    (hT : targetAccuracy.value=T.accuracy) (hP : policyAccuracy.value=P.accuracy)
    (b c o : ℕ) (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (marks : OuterMarkArray n m (Fin o → Bool))
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (k i : Fin n) (x : BinaryRational) (H : BinaryOuterHistory n (Fin n)) :
    let rows := outerRawBlocks (fun i j => (y i j).value)
    let q := countedFiniteOuterPrepare hm T P b c o mu.value zlo.value zhi.value
      (4*(Nat.clog 2 m : ℚ)+2) (fun r i => rows.1 i r) (fun r i => rows.2.1 i r)
      (fun r i => rows.2.2 i r) marks bits
    (countedBinaryLearnerDecision P pa hpa policyAccuracy
      (countedBinaryLearnerPrepare hm T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
        b c o y marks bits) k i x H).1 =
      (countedFiniteOuterDecision P zlo.value zhi.value q k i x.value (binaryOuterHistoryValue H)).1 := by
  unfold countedBinaryLearnerPrepare countedBinaryLearnerDecision
  apply decideBinaryOuterStage_value_of_inner hm T P b c o mu.value zlo.value zhi.value _ y marks bits _ _ k i x H
  intro d v H' _
  let rows := fun i j => d i (finiteTrainingIndex m j)
  let validation := fun j i => d i (finiteValidationIndex m j)
  let q := countedFiniteCalibrationPrepare T P b c mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
    (fun i j => (rows i j).value) (fun r i => (validation r i).value) bits
  have h := countedBinaryBoundedRankDecision_value T P ta pa hta hpa mu zlo zhi targetAccuracy policyAccuracy
    hT hP rows validation b c bits i v H'
  dsimp only at h
  refine h.trans ?_
  change (countedFiniteCalibrationDecision P zlo.value zhi.value q i v.value H').1 =
    (countedFiniteCalibrationDecision P zlo.value zhi.value q i v.value (binaryOuterHistoryValue H')).1
  let f := fun a : Fin n × BinaryRational => (a.1,a.2.value)
  have hSet : onlineContinuationSet q.rows (binaryOuterHistoryValue H') i=onlineContinuationSet q.rows H' i := by
    ext j
    cases he : H' j <;> simp [onlineContinuationSet,binaryOuterHistoryValue,he]
  have hRank : onlineQueryRank (binaryOuterHistoryValue H') i=onlineQueryRank H' i := onlineQueryRank_map H' f i
  unfold countedFiniteCalibrationDecision countedOnlineCalibrationDecision
  rw [hSet,hRank]

end ProphetSecretary.Statistics.Calibration
