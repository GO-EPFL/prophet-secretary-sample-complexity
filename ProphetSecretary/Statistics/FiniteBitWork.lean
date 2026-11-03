import ProphetSecretary.Statistics.FiniteFairBankCall
import ProphetSecretary.Statistics.CalibrationRankDecode
import ProphetSecretary.Statistics.CountedCalibrationPrepare
import ProphetSecretary.Statistics.CountedOnlineCalibration
import ProphetSecretary.Statistics.RationalCalibrationGrid
import ProphetSecretary.Statistics.CalibratedOuter.PreparedExecution
import ProphetSecretary.Statistics.CalibratedOuter.MarkCoupling
import ProphetSecretary.Statistics.CalibratedOuter.Work
import ProphetSecretary.Statistics.CalibratedOuter.TrainingHeight
import ProphetSecretary.Statistics.CalibrationRationalHeight
import ProphetSecretary.Analysis.BinaryPrimitiveWork

/-!
# The counted schedule for the fair-bit learner

The outer and bounded preparations are evaluated once. Validation uses
stored rational rank profiles. The online callback receives the current
identity, current value, and the presence information from the past.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

structure FairCallSchedule where
  bits : ℕ
  level : ℕ
  accuracy : ℚ
  failure : ℚ
  confidence : ∃ j : ℕ, (1/4 : ℚ)^j ≤ failure

abbrev FairCallSchedule.Seed (q : FairCallSchedule) (n : ℕ) :=
  FairQueryBank n q.bits (confidenceCopyCount q.failure q.confidence) q.level

def FairCallSchedule.work (q : FairCallSchedule) (n m : ℕ) : ℕ :=
  rationalFairBankCallWorkBound n m q.bits q.level (confidenceCopyCount q.failure q.confidence)

def countedFiniteTargetCall {n m : ℕ} (s : FairCallSchedule) (y : Fin n → Fin m → ℚ)
    (z : ℚ) (bits : s.Seed n) : ℚ × ℕ :=
  let q := countedRationalFairBankCall y (List.finRange n,1,z)
    s.bits s.level s.accuracy s.failure s.confidence bits
  (q.value,q.work+n+3)

lemma countedFiniteTargetCall_work {n m : ℕ} (s : FairCallSchedule) (y : Fin n → Fin m → ℚ)
    (z : ℚ) (bits : s.Seed n) : (countedFiniteTargetCall s y z bits).2 ≤ s.work n m+n+3 := by
  unfold countedFiniteTargetCall
  have h := countedRationalFairBankCall_work y (List.finRange n,1,z) (List.nodup_finRange n)
    s.bits s.level s.accuracy s.failure s.confidence bits
  exact Nat.add_le_add_right (Nat.add_le_add_right h n) 3

def countedFiniteThresholdCall {n m : ℕ} (s : FairCallSchedule) (y : Fin n → Fin m → ℚ)
    (A : Finset (Fin n)) (u z : ℚ) (bits : s.Seed n) : ℚ × ℕ :=
  let l := countedPredicateFilter (fun i => i ∈ A) (List.finRange n)
  let q := countedRationalFairBankCall y (l.1,u,z)
    s.bits s.level s.accuracy s.failure s.confidence bits
  (q.value,q.work+l.2+10*(n+1)^2)

lemma countedFiniteThresholdCall_work {n m : ℕ} (s : FairCallSchedule) (y : Fin n → Fin m → ℚ)
    (A : Finset (Fin n)) (u z : ℚ) (bits : s.Seed n) :
    (countedFiniteThresholdCall s y A u z bits).2 ≤ s.work n m+1+3*n+10*(n+1)^2 := by
  let l := countedPredicateFilter (fun i => i ∈ A) (List.finRange n)
  have hL : l.1.Nodup := by rw [countedPredicateFilter_value]; exact (List.nodup_finRange n).filter _
  have h := countedRationalFairBankCall_work y (l.1,u,z) hL s.bits s.level s.accuracy s.failure s.confidence bits
  change (countedRationalFairBankCall y (l.1,u,z) s.bits s.level s.accuracy s.failure s.confidence bits).work ≤ s.work n m at h
  have hW : l.2 ≤ 1+3*n := by simpa only [l,List.length_finRange] using
    countedPredicateFilter_work (fun i => i ∈ A) (List.finRange n)
  exact (Nat.add_le_add_right (Nat.add_le_add h hW) _).trans_eq (by omega)

def rankDecodeWorkBound (n m b c : ℕ) : ℕ :=
  m*(rationalValidationOrderWork n b+rationalRankClocksWork n b+4)+
    rationalRankClocksWork n b+10*c+7+8*(m+1)+8

def finiteCalibrationPrepareWorkBound (n m J b c WT WP : ℕ) : ℕ :=
  rankDecodeWorkBound n m b c +
    100*(n+1)^2*(m+1)^2+26*(n+1)*(m+1)+(4*m+1)*(WT+10)+8+
    m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6)+
    10*(m+1)*(J+3)+8*(J+1)+4*(J+2)+2*c+42

structure FiniteCalibrationPreparation (n m J : ℕ) (PSeed : Type) where
  rows : Fin n → Fin m → ℚ
  selected : Fin (J+1)
  fallback : Bool
  clocks : Fin n → ℚ
  queryBits : PolicyQueryArray n J PSeed
  work : ℕ

def countedFiniteCalibrationPrepare {n m J : ℕ} (T P : FairCallSchedule) (b c : ℕ)
    (mu zlo zhi Lbar : ℚ) (y : Fin n → Fin m → ℚ) (x : Fin m → Fin n → ℚ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    FiniteCalibrationPreparation n m J (P.Seed n) :=
  let d := countedDecodeRankCalibrationBits b c bits
  let q := countedCalibrationPrepare mu zlo zhi Lbar (countedFiniteTargetCall T y)
    (countedFiniteThresholdCall P y) y d.1.1
    (fun j => ((d.1.2.1 j).1,x j,(d.1.2.1 j).2.1,(d.1.2.1 j).2.2))
  let grid := countedBitGridSize c
  let α := rationalMixtureGridRound grid.1 (by dsimp [grid]; rw [countedBitGridSize_value]; positivity) q.selection.2
  let j := if d.1.2.2.2.2 < α then upperPolicyIndex J q.selection.1
    else lowerPolicyIndex J q.selection.1
  ⟨q.rows,j,q.fallback,d.1.2.2.1,d.1.2.2.2.1,d.2+q.work+grid.2+26⟩

theorem countedFiniteCalibrationPrepare_work {n m J : ℕ} (T P : FairCallSchedule) (b c : ℕ)
    (mu zlo zhi Lbar : ℚ) (y : Fin n → Fin m → ℚ) (x : Fin m → Fin n → ℚ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    (countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar y x bits).work ≤
      finiteCalibrationPrepareWorkBound n m J b c (T.work n m+n+3) (P.work n m+1+3*n+10*(n+1)^2) := by
  let d := countedDecodeRankCalibrationBits b c bits
  let profile := fun j => ((d.1.2.1 j).1,x j,(d.1.2.1 j).2.1,(d.1.2.1 j).2.2)
  let q := countedCalibrationPrepare mu zlo zhi Lbar (countedFiniteTargetCall T y)
    (countedFiniteThresholdCall P y) y d.1.1 profile
  have hD : d.2 ≤ rankDecodeWorkBound n m b c := countedDecodeRankCalibrationBits_work b c bits
  have hQ := countedCalibrationPrepare_work mu zlo zhi Lbar (countedFiniteTargetCall T y)
    (countedFiniteThresholdCall P y) y d.1.1 profile (T.work n m+n+3) (P.work n m+1+3*n+10*(n+1)^2)
    (countedFiniteTargetCall_work T y) (countedFiniteThresholdCall_work P y)
  change d.2+q.work+(countedBitGridSize c).2+26 ≤ _
  rw [countedBitGridSize_work]
  exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hD hQ) _) _).trans_eq
    (by unfold finiteCalibrationPrepareWorkBound; ring)

def countedFiniteCalibrationDecision {n m J : ℕ} {Obs : Type*} (P : FairCallSchedule) (zlo zhi : ℚ)
    (q : FiniteCalibrationPreparation n m J (P.Seed n)) (i : Fin n) (x : ℚ)
    (H : Fin n → Option Obs) : Bool × ℕ :=
  let k := onlineQueryRank H i
  let r := countedOnlineCalibrationDecision (storedCalibrationCoefficient J zlo zhi)
    (countedFiniteThresholdCall P q.rows) q.rows q.fallback q.selected (q.clocks k) x H i q.queryBits
  (r.1,r.2+4*n+8)

def finiteCalibrationDecisionWorkBound (n m J WP : ℕ) : ℕ :=
  n*(m+4)+18+4*n+(J+1)*(WP+2)

lemma countedFiniteCalibrationDecision_work {n m J : ℕ} {Obs : Type*} (P : FairCallSchedule) (zlo zhi : ℚ)
    (q : FiniteCalibrationPreparation n m J (P.Seed n)) (i : Fin n) (x : ℚ) (H : Fin n → Option Obs) :
    (countedFiniteCalibrationDecision P zlo zhi q i x H).2 ≤
      finiteCalibrationDecisionWorkBound n m J (P.work n m+1+3*n+10*(n+1)^2) := by
  have h := countedOnlineCalibrationDecision_work_le (storedCalibrationCoefficient J zlo zhi)
    (countedFiniteThresholdCall P q.rows) q.rows q.fallback q.selected
    (q.clocks (onlineQueryRank H i)) x H i q.queryBits (P.work n m+1+3*n+10*(n+1)^2)
    (countedFiniteThresholdCall_work P q.rows)
  change (countedOnlineCalibrationDecision (storedCalibrationCoefficient J zlo zhi)
    (countedFiniteThresholdCall P q.rows) q.rows q.fallback q.selected
    (q.clocks (onlineQueryRank H i)) x H i q.queryBits).2+4*n+8 ≤ _
  unfold finiteCalibrationDecisionWorkBound
  omega

private lemma finiteVectorGet_ofFn {α : Type*} {K : ℕ} (f : Fin K → α) (i : Fin K) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

def countedFiniteOuterMarks {n m : ℕ} (b : ℕ)
    (bits : Fin (outerMarkSlotCount n m) → Fin b → Bool) : OuterMarks n m ℚ × ℕ :=
  let q := Vector.ofFn (fun i => countedStoredDyadicUniform b (bits i))
  (unpackOuterMarks (fun i => (q.get i).1),
    (∑ i : Fin (outerMarkSlotCount n m), (q.get i).2)+8*outerMarkSlotCount n m+5)

lemma countedFiniteOuterMarks_work {n m : ℕ} (b : ℕ)
    (bits : Fin (outerMarkSlotCount n m) → Fin b → Bool) :
    (countedFiniteOuterMarks b bits).2 = outerMarkSlotCount n m*(10*b+15)+5 := by
  simp [countedFiniteOuterMarks,finiteVectorGet_ofFn,countedStoredDyadicUniform_work]
  ring

structure FiniteOuterPreparation (n m J : ℕ) (PSeed : Type) where
  outer : CountedOuterPreparation ℚ n m
  onlineTags : Fin n → ℚ
  calibration : Option (FiniteCalibrationPreparation n m J PSeed)
  work : ℕ

def finiteTrainingIndex (m : ℕ) (j : Fin m) : Fin (2*m) := ⟨j.val,by have := j.isLt; omega⟩

def finiteValidationIndex (m : ℕ) (j : Fin m) : Fin (2*m) := ⟨m+j.val,by have := j.isLt; omega⟩

def countedFiniteOuterPrepare {n m J : ℕ} (hm : 1≤m) (T P : FairCallSchedule) (b c o : ℕ)
    (mu zlo zhi Lbar : ℚ) (cut : Fin m → Fin n → ℚ)
    (pilot : Fin (outerPilotRounds m) → Fin n → ℚ) (inner : Fin (2*m) → Fin n → ℚ)
    (marks : Fin (outerMarkSlotCount n m) → Fin o → Bool)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    FiniteOuterPreparation n m J (P.Seed n) :=
  let tags := countedFiniteOuterMarks o marks
  let q := countedOuterPrepare hm (fun r i => (cut r i,tags.1.1 r i))
    (fun r i => (pilot r i,tags.1.2.1 r i)) (fun r i => (inner r i,tags.1.2.2.1 r i))
  if q.pilot=0 then ⟨q,tags.1.2.2.2,none,tags.2+q.work+4⟩ else
    let p := countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
      (fun i j => q.displayed i (finiteTrainingIndex m j))
      (fun j i => q.displayed i (finiteValidationIndex m j)) bits
    ⟨q,tags.1.2.2.2,some p,tags.2+q.work+p.work+4⟩

def finiteOuterPrepareWorkBound (n m J b c o WT WP : ℕ) : ℕ :=
  outerMarkSlotCount n m*(10*o+15)+5+
  (10*(m+1)*(n+1)+20*(outerPilotRounds m+1)^2*(n+1)+5+n*(2*m)*(4*m+21))+
    finiteCalibrationPrepareWorkBound n m J b c WT WP+4

theorem countedFiniteOuterPrepare_work {n m J : ℕ} (hm : 1≤m) (T P : FairCallSchedule) (b c o : ℕ)
    (mu zlo zhi Lbar : ℚ) (cut : Fin m → Fin n → ℚ)
    (pilot : Fin (outerPilotRounds m) → Fin n → ℚ) (inner : Fin (2*m) → Fin n → ℚ)
    (marks : Fin (outerMarkSlotCount n m) → Fin o → Bool)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    (countedFiniteOuterPrepare hm T P b c o mu zlo zhi Lbar cut pilot inner marks bits).work ≤
      finiteOuterPrepareWorkBound n m J b c o (T.work n m+n+3) (P.work n m+1+3*n+10*(n+1)^2) := by
  let tags := countedFiniteOuterMarks o marks
  let q := countedOuterPrepare hm (fun r i => (cut r i,tags.1.1 r i))
    (fun r i => (pilot r i,tags.1.2.1 r i)) (fun r i => (inner r i,tags.1.2.2.1 r i))
  have hT : tags.2 = outerMarkSlotCount n m*(10*o+15)+5 := countedFiniteOuterMarks_work o marks
  have hQ := countedOuterPrepare_work hm (fun r i => (cut r i,tags.1.1 r i))
    (fun r i => (pilot r i,tags.1.2.1 r i)) (fun r i => (inner r i,tags.1.2.2.1 r i))
  have hP := countedFiniteCalibrationPrepare_work T P b c mu zlo zhi Lbar
    (fun i j => q.displayed i (finiteTrainingIndex m j))
    (fun j i => q.displayed i (finiteValidationIndex m j)) bits
  change (if q.pilot=0 then _ else _ : FiniteOuterPreparation n m J (P.Seed n)).work ≤ _
  unfold finiteOuterPrepareWorkBound
  have h' : q.work ≤ 10*(m+1)*(n+1)+20*(outerPilotRounds m+1)^2*(n+1)+5+n*(2*m)*(4*m+21) := hQ
  by_cases he : q.pilot=0
  · rw [if_pos he]
    change tags.2+q.work+4 ≤ _
    omega
  · rw [if_neg he]
    change tags.2+q.work+(countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
      (fun i j => q.displayed i (finiteTrainingIndex m j))
      (fun j i => q.displayed i (finiteValidationIndex m j)) bits).work+4 ≤ _
    omega

def countedFiniteOuterDecision {n m J : ℕ} {Time : Type*} (P : FairCallSchedule) (zlo zhi : ℚ)
    (p : FiniteOuterPreparation n m J (P.Seed n)) (t : Time) (i : Fin n) (x : ℚ)
    (H : Fin n → Option (Time × ℚ)) : Bool × ℕ :=
  countedOuterOnline p.outer p.onlineTags (fun _ j y past =>
    match p.calibration with
    | none => (false,1)
    | some q => countedFiniteCalibrationDecision P zlo zhi q j y past) t i x H

def finiteOuterDecisionWorkBound (n m J WP : ℕ) : ℕ :=
  finiteCalibrationDecisionWorkBound n m J WP+(n+1)*(4*m+24)+9

lemma countedFiniteOuterDecision_work {n m J : ℕ} {Time : Type*} (P : FairCallSchedule) (zlo zhi : ℚ)
    (p : FiniteOuterPreparation n m J (P.Seed n)) (t : Time) (i : Fin n) (x : ℚ)
    (H : Fin n → Option (Time × ℚ)) :
    (countedFiniteOuterDecision P zlo zhi p t i x H).2 ≤
      finiteOuterDecisionWorkBound n m J (P.work n m+1+3*n+10*(n+1)^2) := by
  unfold countedFiniteOuterDecision finiteOuterDecisionWorkBound
  apply countedOuterOnline_work
  intro y h
  cases he : p.calibration with
  | none => change 1≤_; unfold finiteCalibrationDecisionWorkBound; omega
  | some q => exact countedFiniteCalibrationDecision_work P zlo zhi q i y h

/-- Accounting is over the actually invoked prefix callbacks. The input to
each decision is its own history; the list of calls is only used for the
hard work bound. -/
def countedFiniteScheduleWork {n m J K : ℕ} {Time : Type*} (P : FairCallSchedule) (zlo zhi : ℚ)
    (p : FiniteOuterPreparation n m J (P.Seed n))
    (calls : Fin K → Time × (Fin n × (ℚ × (Fin n → Option (Time × ℚ))))) : ℕ :=
  p.work + ∑ k, let a := calls k
    (countedFiniteOuterDecision P zlo zhi p a.1 a.2.1 a.2.2.1 a.2.2.2).2

lemma countedFiniteScheduleWork_le {n m J K : ℕ} {Time : Type*} (P : FairCallSchedule) (zlo zhi : ℚ)
    (p : FiniteOuterPreparation n m J (P.Seed n)) (hK : K≤n)
    (calls : Fin K → Time × (Fin n × (ℚ × (Fin n → Option (Time × ℚ))))) :
    countedFiniteScheduleWork P zlo zhi p calls ≤
      p.work+n*finiteOuterDecisionWorkBound n m J (P.work n m+1+3*n+10*(n+1)^2) := by
  unfold countedFiniteScheduleWork
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _k : Fin K, finiteOuterDecisionWorkBound n m J (P.work n m+1+3*n+10*(n+1)^2) :=
      Finset.sum_le_sum (fun k _ => countedFiniteOuterDecision_work P zlo zhi p
        (calls k).1 (calls k).2.1 (calls k).2.2.1 (calls k).2.2.2)
    _ ≤ _ := by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      Nat.mul_le_mul_right (finiteOuterDecisionWorkBound n m J (P.work n m+1+3*n+10*(n+1)^2)) hK

abbrev FiniteScheduleClocks (n m b c : ℕ) :=
  (Fin m → RankCalibrationClockBits n b × RankCalibrationClockBits n b) ×
    (RankCalibrationClockBits n b × (Fin c → Bool))

def attachScheduleClocks {n m J b c : ℕ} {T P : Type}
    (x : CalibrationQueryArrays n m J T P) (u : FiniteScheduleClocks n m b c) :
    RankCalibrationBits n m J b c T P :=
  (x.1,(fun j => ((u.1 j).1,(u.1 j).2,x.2.1 j)),u.2.1,x.2.2,u.2.2)

def finiteQueryStorageBound (n m J : ℕ) (T P : FairCallSchedule) : ℕ :=
  (4*m+1)*fairQueryBankWorkBound n T.bits (confidenceCopyCount T.failure T.confidence) T.level +
    (m+1)*n*(J+1)*fairQueryBankWorkBound n P.bits (confidenceCopyCount P.failure P.confidence) P.level +
    10*((4*m+1)+(m+1)*(n*(J+1))+m+1)+6

def finiteScheduleArithmeticBound (n m J b c o : ℕ) (T P : FairCallSchedule) : ℕ :=
  finiteQueryStorageBound n m J T P +
    finiteOuterPrepareWorkBound n m J b c o (T.work n m+n+3) (P.work n m+1+3*n+10*(n+1)^2) +
    n*finiteOuterDecisionWorkBound n m J (P.work n m+1+3*n+10*(n+1)^2)

def finiteScheduleFairBitsBound (n m J b c o : ℕ) (T P : FairCallSchedule) : ℕ :=
  (4*m+1)*(5*confidenceCopyCount T.failure T.confidence*16^T.level*((3*n+2)*T.bits))+
    (m+1)*n*(J+1)*(5*confidenceCopyCount P.failure P.confidence*16^P.level*((3*n+2)*P.bits))+
    outerMarkSlotCount n m*o + n*(2*m+1)*b+c

structure FiniteScheduleRun (n m J : ℕ) (PSeed : Type) where
  prepared : FiniteOuterPreparation n m J PSeed
  arithmeticWork : ℕ
  fairBits : ℕ

def countedFiniteSchedule {n m J K : ℕ} {Time : Type*} (hm : 1≤m) (T P : FairCallSchedule) (b c o : ℕ)
    (mu zlo zhi Lbar : ℚ) (cut : Fin m → Fin n → ℚ)
    (pilot : Fin (outerPilotRounds m) → Fin n → ℚ) (inner : Fin (2*m) → Fin n → ℚ)
    (marks : Fin (outerMarkSlotCount n m) → Fin o → Bool) (clocks : FiniteScheduleClocks n m b c)
    (drawBit : StateM ℕ Bool) (initial : ℕ)
    (calls : Fin K → Time × (Fin n × (ℚ × (Fin n → Option (Time × ℚ))))) :
    FiniteScheduleRun n m J (P.Seed n) :=
  let r := (sampleCalibrationQueryArraysM n m J T.bits (confidenceCopyCount T.failure T.confidence) T.level
    P.bits (confidenceCopyCount P.failure P.confidence) P.level drawBit).run initial
  let q := countedFiniteOuterPrepare hm T P b c o mu zlo zhi Lbar cut pilot inner marks
    (attachScheduleClocks r.1.1 clocks)
  ⟨q,r.1.2+countedFiniteScheduleWork P zlo zhi q calls,
    r.2-initial+outerMarkSlotCount n m*o+n*(2*m+1)*b+c⟩

/-- The native schedule has a hard operation and fair-bit budget on every
input and every invoked prefix sequence of length at most the instance size. -/
theorem countedFiniteSchedule_work {n m J K : ℕ} {Time : Type*} (hm : 1≤m) (T P : FairCallSchedule) (b c o : ℕ)
    (mu zlo zhi Lbar : ℚ) (cut : Fin m → Fin n → ℚ)
    (pilot : Fin (outerPilotRounds m) → Fin n → ℚ) (inner : Fin (2*m) → Fin n → ℚ)
    (marks : Fin (outerMarkSlotCount n m) → Fin o → Bool) (clocks : FiniteScheduleClocks n m b c)
    (drawBit : StateM ℕ Bool) (initial : ℕ) (hDraw : ∀ a, (drawBit.run a).2=a+1) (hK : K≤n)
    (calls : Fin K → Time × (Fin n × (ℚ × (Fin n → Option (Time × ℚ))))) :
    let q := countedFiniteSchedule (J := J) hm T P b c o mu zlo zhi Lbar cut pilot inner marks clocks drawBit initial calls
    q.arithmeticWork ≤ finiteScheduleArithmeticBound n m J b c o T P ∧
      q.fairBits ≤ finiteScheduleFairBitsBound n m J b c o T P := by
  let CT := confidenceCopyCount T.failure T.confidence
  let CP := confidenceCopyCount P.failure P.confidence
  let r := (sampleCalibrationQueryArraysM n m J T.bits CT T.level P.bits CP P.level drawBit).run initial
  let bits := attachScheduleClocks r.1.1 clocks
  let q := countedFiniteOuterPrepare hm T P b c o mu zlo zhi Lbar cut pilot inner marks bits
  have hR : r.1.2 ≤ finiteQueryStorageBound n m J T P :=
    sampleCalibrationQueryArraysM_work n m J T.bits CT T.level P.bits CP P.level drawBit initial
  have hP := countedFiniteOuterPrepare_work hm T P b c o mu zlo zhi Lbar cut pilot inner marks bits
  have hW := countedFiniteScheduleWork_le P zlo zhi q hK calls
  have hF := sampleCalibrationQueryArraysM_counter_le n m J T.bits CT T.level P.bits CP P.level drawBit hDraw initial
  refine ⟨?_,?_⟩
  · change r.1.2+countedFiniteScheduleWork P zlo zhi q calls ≤ _
    unfold finiteScheduleArithmeticBound
    have hP' : q.work ≤ finiteOuterPrepareWorkBound n m J b c o (T.work n m+n+3) (P.work n m+1+3*n+10*(n+1)^2) := hP
    omega
  · change r.2-initial+outerMarkSlotCount n m*o+n*(2*m+1)*b+c ≤ _
    change r.2 ≤ initial+(4*m+1)*(5*CT*16^T.level*((3*n+2)*T.bits))+
      (m+1)*n*(J+1)*(5*CP*16^P.level*((3*n+2)*P.bits)) at hF
    change _ ≤ (4*m+1)*(5*CT*16^T.level*((3*n+2)*T.bits))+
      (m+1)*n*(J+1)*(5*CP*16^P.level*((3*n+2)*P.bits))+
      outerMarkSlotCount n m*o+n*(2*m+1)*b+c
    omega

def finiteScheduleBitWorkBound (n m J b c o B : ℕ) (T P : FairCallSchedule) : ℕ :=
  finiteScheduleArithmeticBound n m J b c o T P*binaryPrimitiveCharge B +
    finiteScheduleFairBitsBound n m J b c o T P

/-- A primitive replay of the counted schedule is charged by the exact
binary routines. The replay hypotheses identify its primitive calls and
the widths of their actual operands. -/
theorem finiteSchedule_binaryReplay_work {n m J : ℕ} {PSeed : Type}
    (run : FiniteScheduleRun n m J PSeed) (T P : FairCallSchedule) (b c o B : ℕ)
    (hw : run.arithmeticWork ≤ finiteScheduleArithmeticBound n m J b c o T P)
    (hb : run.fairBits ≤ finiteScheduleFairBitsBound n m J b c o T P)
    (trace : List BinaryPrimitive) (hTrace : trace.length ≤ run.arithmeticWork)
    (hWidth : ∀ q ∈ trace, q.Fits B) :
    binaryPrimitiveTraceWork trace + run.fairBits ≤ finiteScheduleBitWorkBound n m J b c o B T P := by
  exact Nat.add_le_add ((binaryPrimitiveTraceWork_le trace B hWidth).trans
    (Nat.mul_le_mul_right _ (hTrace.trans hw))) hb

end ProphetSecretary.Statistics.Calibration
