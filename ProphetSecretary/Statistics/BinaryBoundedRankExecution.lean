import ProphetSecretary.Statistics.BinaryFiniteCalibration
import ProphetSecretary.Statistics.BinaryCalibrationRandomness
import ProphetSecretary.Statistics.FiniteBitOperands

/-!
# The bounded binary rank algorithm

The stored clock list supplies annotations at the observed rank.
Training and all validation scans finish before the first online
decision. The value theorem compares both executions on the same
finite random words.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m J : ℕ}

structure BinaryBoundedRankPreparation (n m J : ℕ) (Seed : Type) where
  calibration : BinaryCalibrationPreparation n m J
  onlineTimes : Fin n → CalibrationBinary
  onlineQueries : PolicyQueryArray n J Seed
  work : ℕ

def countedBinaryBoundedRankPrepare (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : CalibrationBinary)
    (y : Fin n → Fin m → CalibrationBinary) (x : Fin m → Fin n → CalibrationBinary)
    (b c : ℕ) (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    BinaryBoundedRankPreparation n m J (P.Seed n) :=
  let d := countedBinaryRankCalibrationSeed b c bits
  let a := countedBinaryFiniteCalibrationPrepareCached T P ta pa ht hp mu zlo zhi
    d.coinGrid targetAccuracy policyAccuracy d.coinLast d.coinWord y d.target
    (fun r => ((d.validation r).1,x r,(d.validation r).2.1,(d.validation r).2.2))
  ⟨a,d.onlineTimes,d.onlineQueries,d.work+a.work+4⟩

def countedBinaryBoundedRankDecision {Obs : Type}
    (P : FairCallSchedule) (pa : ℕ) (hp : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryBoundedRankPreparation n m J (P.Seed n))
    (i : Fin n) (x : CalibrationBinary) (H : Fin n → Option Obs) : Bool×ℕ :=
  let t := q.onlineTimes (onlineQueryRank H i)
  let r := countedBinaryFiniteCalibrationDecisionCached P pa hp y policyAccuracy q.calibration
    t x H i q.onlineQueries
  (r.1,r.2+n+3)

private lemma countedRankSeed_target (T P : FairCallSchedule) (b c : ℕ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    (countedBinaryRankCalibrationSeed b c bits).target=(countedDecodeRankCalibrationBits b c bits).1.1 :=
  rfl

private lemma countedRankSeed_onlineQueries (T P : FairCallSchedule) (b c : ℕ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    (countedBinaryRankCalibrationSeed b c bits).onlineQueries=(countedDecodeRankCalibrationBits b c bits).1.2.2.2.1 :=
  rfl

theorem countedBinaryBoundedRankPrepare_value (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : CalibrationBinary)
    (hT : targetAccuracy.value=T.accuracy) (hP : policyAccuracy.value=P.accuracy)
    (y : Fin n → Fin m → CalibrationBinary) (x : Fin m → Fin n → CalibrationBinary)
    (b c : ℕ) (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) :
    let Q := countedBinaryBoundedRankPrepare T P ta pa ht hp mu zlo zhi targetAccuracy policyAccuracy y x b c bits
    let yQ := fun i j => (y i j).value
    let q := countedFiniteCalibrationPrepare T P b c mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
      yQ (fun r i => (x r i).value) bits
    Q.calibration.fallback=q.fallback ∧ Q.calibration.selected=q.selected ∧ q.rows=yQ ∧
      (fun k => (Q.onlineTimes k).value)=q.clocks ∧ Q.onlineQueries=q.queryBits ∧
      Q.calibration.active=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<yQ i j))=true) ∧
      (∀ k,(Q.calibration.parameters.coefficient k).value=storedCalibrationCoefficient J zlo.value zhi.value k) := by
  let D := countedBinaryRankCalibrationSeed b c bits
  let d := (countedDecodeRankCalibrationBits b c bits).1
  let yQ := fun i j => (y i j).value
  let v := fun r : Fin m => ((D.validation r).1,x r,(D.validation r).2.1,(D.validation r).2.2)
  let V := fun r : Fin m => ((d.2.1 r).1,(fun i => (x r i).value),(d.2.1 r).2.1,(d.2.1 r).2.2)
  have hv : (fun r => binaryCalibrationRankProfileValue (v r))=V := by
    funext r
    obtain ⟨h₁,h₂,h₃⟩ := countedBinaryRankCalibrationSeed_validation b c bits r
    unfold v V binaryCalibrationRankProfileValue
    dsimp only
    rw [h₁,h₂,h₃]
  obtain ⟨htime,hquery,hscale,hlast,hcoin⟩ := countedBinaryRankCalibrationSeed_online b c bits
  let a := countedBinaryFiniteCalibrationPrepare T P mu zlo zhi D.coinGrid targetAccuracy policyAccuracy
    D.coinLast D.coinWord y D.target v
  have ha := countedBinaryFiniteCalibrationPrepare_value T P mu zlo zhi D.coinGrid targetAccuracy policyAccuracy
    D.coinLast D.coinWord hT hP y D.target v (2^c) (by positivity) hscale hlast
  rw [hv,countedRankSeed_target T P b c bits] at ha
  let q := countedCalibrationPrepare mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
    (countedFiniteTargetCall T yQ) (countedFiniteThresholdCall P yQ) yQ d.1 V
  have hc : (binaryWordValue D.coinWord:ℚ)/((2^c:ℕ):ℚ)=d.2.2.2.2 := by
    rw [hcoin]
    change _=(countedStoredDyadicUniform c bits.2.2.2.2).1
    simp only [countedStoredDyadicUniform_value,countedDyadicUniform,countedFairBitsIndex_value,gridPoint]
  have hsel : a.selected =
      (if d.2.2.2.2<rationalMixtureGridRound (countedBitGridSize c).1
        (by rw [countedBitGridSize_value]; positivity) q.selection.2
       then upperPolicyIndex J q.selection.1 else lowerPolicyIndex J q.selection.1) := by
    have hRound (N : ℕ) (hN : 0<N) (hN' : N=2^c) :
        rationalMixtureGridRound N hN q.selection.2=
          rationalMixtureGridRound (2^c) (by positivity) q.selection.2 := by
      subst N
      rfl
    rw [hRound _ _ (countedBitGridSize_value c)]
    have hh := ha.2.1
    change (countedBinaryFiniteCalibrationPrepare T P mu zlo zhi D.coinGrid targetAccuracy policyAccuracy
      D.coinLast D.coinWord y d.1 v).selected =
        (if (binaryWordValue D.coinWord:ℚ)/((2^c:ℕ):ℚ)<rationalMixtureGridRound (2^c) (by positivity) q.selection.2
        then upperPolicyIndex J q.selection.1 else lowerPolicyIndex J q.selection.1) at hh
    rw [hc,←countedRankSeed_target T P b c bits] at hh
    exact hh
  have hCoeff : ∀ k,(a.parameters.coefficient k).value=
      storedCalibrationCoefficient J zlo.value zhi.value k :=
    countedBinaryFiniteCalibrationPrepare_coefficient T P mu zlo zhi D.coinGrid targetAccuracy policyAccuracy
      D.coinLast D.coinWord y D.target v
  dsimp only
  unfold countedBinaryBoundedRankPrepare
  dsimp only
  rw [countedBinaryFiniteCalibrationPrepareCached_eq]
  exact ⟨ha.1,hsel,rfl,htime,countedRankSeed_onlineQueries T P b c bits,ha.2.2,hCoeff⟩

theorem countedBinaryBoundedRankDecision_value {Obs : Type} (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : CalibrationBinary)
    (hT : targetAccuracy.value=T.accuracy) (hP : policyAccuracy.value=P.accuracy)
    (y : Fin n → Fin m → CalibrationBinary) (x : Fin m → Fin n → CalibrationBinary)
    (b c : ℕ) (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (i : Fin n) (a : CalibrationBinary) (H : Fin n → Option Obs) :
    let Q := countedBinaryBoundedRankPrepare T P ta pa ht hp mu zlo zhi targetAccuracy policyAccuracy y x b c bits
    let q := countedFiniteCalibrationPrepare T P b c mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
      (fun i j => (y i j).value) (fun r i => (x r i).value) bits
    (countedBinaryBoundedRankDecision P pa hp y policyAccuracy Q i a H).1 =
      (countedFiniteCalibrationDecision P zlo.value zhi.value q i a.value H).1 := by
  let Q := countedBinaryBoundedRankPrepare T P ta pa ht hp mu zlo zhi targetAccuracy policyAccuracy y x b c bits
  let q := countedFiniteCalibrationPrepare T P b c mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
    (fun i j => (y i j).value) (fun r i => (x r i).value) bits
  have hh := countedBinaryBoundedRankPrepare_value T P ta pa ht hp mu zlo zhi targetAccuracy policyAccuracy
    hT hP y x b c bits
  have hFallback : Q.calibration.fallback=q.fallback := hh.1
  have hSelected : Q.calibration.selected=q.selected := hh.2.1
  have hRows : q.rows=fun i j => (y i j).value := hh.2.2.1
  have hTimes : (fun k => (Q.onlineTimes k).value)=q.clocks := hh.2.2.2.1
  have hQueries : Q.onlineQueries=q.queryBits := hh.2.2.2.2.1
  have hActive := hh.2.2.2.2.2.1
  have hCoeff := hh.2.2.2.2.2.2
  change (countedBinaryBoundedRankDecision P pa hp y policyAccuracy Q i a H).1 =
    (countedFiniteCalibrationDecision P zlo.value zhi.value q i a.value H).1
  unfold countedBinaryBoundedRankDecision countedFiniteCalibrationDecision
  dsimp only
  rw [countedBinaryFiniteCalibrationDecisionCached_eq,
    countedBinaryFiniteCalibrationDecision_value P y policyAccuracy Q.calibration zlo.value zhi.value
      (Q.onlineTimes (onlineQueryRank H i)) a H i Q.onlineQueries hP hCoeff hActive,
    hFallback,hSelected,hRows,hQueries,congrFun hTimes]

lemma countedBinaryRankCalibrationSeed_validation_height (b c : ℕ)
    {T P : Type} (bits : RankCalibrationBits n m J b c T P) (r : Fin m) (i : Fin n) :
    RationalHeight (((countedBinaryRankCalibrationSeed b c bits).validation r).2.1 i).value b := by
  rw [congrFun (countedBinaryRankCalibrationSeed_validation b c bits r).2.1]
  simp only [countedDecodeRankCalibrationBits,calibrationVectorGet_ofFn,countedRationalRankValidation]
  exact countedRationalRankClocks_height b (bits.2.1 r).2.1 i

lemma countedBinaryRankCalibrationSeed_online_height (b c : ℕ)
    {T P : Type} (bits : RankCalibrationBits n m J b c T P) (i : Fin n) :
    RationalHeight ((countedBinaryRankCalibrationSeed b c bits).onlineTimes i).value b := by
  rw [congrFun (countedBinaryRankCalibrationSeed_online b c bits).1]
  exact countedRationalRankClocks_height b bits.2.2.1 i

def binaryBoundedRankPrepareWork (T P : FairCallSchedule)
    (n m J b c Y M D K HT HP : ℕ) : ℕ :=
  m*(2*binaryRankOrderWorkBound n b+6)+binaryRankOrderWorkBound n b+110*(c+3)^3+4*c+10+
    finiteBinaryCalibrationPrepareWork T P n m J Y M b D K c HT HP+4

theorem countedBinaryBoundedRankPrepare_work (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : CalibrationBinary)
    (y : Fin n → Fin m → CalibrationBinary) (x : Fin m → Fin n → CalibrationBinary)
    (b c : ℕ) (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (Y M D K HT HP : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (hX : ∀ j i,RationalHeight (x j i).value Y)
    (hm : m≤2^M) (hJ : J≤2^K) (hmu : RationalHeight mu.value D)
    (hlo : RationalHeight zlo.value D) (hhi : RationalHeight zhi.value D)
    (hT : RationalHeight targetAccuracy.value HT) (hP : RationalHeight policyAccuracy.value HP) :
    (countedBinaryBoundedRankPrepare T P ta pa ht hp mu zlo zhi targetAccuracy policyAccuracy
      y x b c bits).work≤binaryBoundedRankPrepareWork T P n m J b c Y M D K HT HP := by
  let d := countedBinaryRankCalibrationSeed b c bits
  let v := fun r : Fin m => ((d.validation r).1,x r,(d.validation r).2.1,(d.validation r).2.2)
  have hd := countedBinaryRankCalibrationSeed_work b c bits
  have hScale : RationalHeight d.coinGrid.value c := by
    rw [(countedBinaryRankCalibrationSeed_online b c bits).2.2.1]
    exact rationalHeight_natCast (2^c) c le_rfl
  have hLast : d.coinLast.length≤c := by simp [d,countedBinaryRankCalibrationSeed]
  have hCoin : d.coinWord.length≤c := by simp [d,countedBinaryRankCalibrationSeed]
  have hA := countedBinaryFiniteCalibrationPrepare_work T P mu zlo zhi d.coinGrid targetAccuracy policyAccuracy
    d.coinLast d.coinWord y d.target v Y M b D K c HT HP hY hm hJ hmu hlo hhi hScale hLast hCoin hT hP
    (countedBinaryRankCalibrationSeed_validation_height b c bits) hX
  unfold countedBinaryBoundedRankPrepare
  dsimp only
  rw [countedBinaryFiniteCalibrationPrepareCached_eq]
  change d.work+(countedBinaryFiniteCalibrationPrepare T P mu zlo zhi d.coinGrid targetAccuracy policyAccuracy
    d.coinLast d.coinWord y d.target v).work+4≤_
  change d.work≤_ at hd
  unfold binaryBoundedRankPrepareWork
  omega

def binaryBoundedRankDecisionWork (P : FairCallSchedule)
    (n m J b Y M D K HP : ℕ) : ℕ :=
  finiteBinaryCalibrationDecisionWork P n m J Y M b D K HP+n+3

theorem countedBinaryBoundedRankDecision_work {Obs : Type} (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi targetAccuracy policyAccuracy : CalibrationBinary)
    (y : Fin n → Fin m → CalibrationBinary) (x : Fin m → Fin n → CalibrationBinary)
    (b c : ℕ) (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (i : Fin n) (a : CalibrationBinary) (H : Fin n → Option Obs)
    (Y M D K HP : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (ha : RationalHeight a.value Y)
    (hm : m≤2^M) (hJ : J≤2^K)
    (hlo : RationalHeight zlo.value D) (hhi : RationalHeight zhi.value D)
    (hP : RationalHeight policyAccuracy.value HP) :
    let Q := countedBinaryBoundedRankPrepare T P ta pa ht hp mu zlo zhi targetAccuracy policyAccuracy y x b c bits
    (countedBinaryBoundedRankDecision P pa hp y policyAccuracy Q i a H).2 ≤
      binaryBoundedRankDecisionWork P n m J b Y M D K HP := by
  let d := countedBinaryRankCalibrationSeed b c bits
  let v := fun r : Fin m => ((d.validation r).1,x r,(d.validation r).2.1,(d.validation r).2.2)
  let Q := countedBinaryFiniteCalibrationPrepare T P mu zlo zhi d.coinGrid targetAccuracy policyAccuracy
    d.coinLast d.coinWord y d.target v
  have hCoeff := countedBinaryFiniteCalibrationPrepare_coefficient T P mu zlo zhi d.coinGrid
    targetAccuracy policyAccuracy d.coinLast d.coinWord y d.target v
  have h := countedBinaryFiniteCalibrationDecision_work P y policyAccuracy Q zlo zhi
    (d.onlineTimes (onlineQueryRank H i)) a H i d.onlineQueries Y M b D K HP hY hm hJ
    hlo hhi (countedBinaryRankCalibrationSeed_online_height b c bits _) ha hP hCoeff
  unfold countedBinaryBoundedRankDecision countedBinaryBoundedRankPrepare
  dsimp only
  rw [countedBinaryFiniteCalibrationDecisionCached_eq,countedBinaryFiniteCalibrationPrepareCached_eq]
  exact Nat.add_le_add_right (Nat.add_le_add_right h n) 3

end ProphetSecretary.Statistics.Calibration
