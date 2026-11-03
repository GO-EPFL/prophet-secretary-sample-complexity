import ProphetSecretary.Statistics.BinaryCalibrationPrepare
import ProphetSecretary.Statistics.BinaryCalibrationCalls
import ProphetSecretary.Statistics.CalibrationRationalHeight

/-!
# The finite binary calibration algorithm

The two counted query algorithms instantiate the target and threshold
calls. Their output widths are fixed from the smaller input widths before
bounding the calibration arithmetic.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {n m J : ℕ}

def countedBinaryFiniteCalibrationPrepare (T P : FairCallSchedule)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → T.Seed n)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (P.Seed n)) :
    BinaryCalibrationPreparation n m J :=
  countedBinaryCalibrationPrepare mu zlo zhi scale last coin
    (countedBinaryFiniteTargetCall T y targetAccuracy)
    (countedBinaryFiniteThresholdCall P y policyAccuracy) y seed profiles

theorem countedBinaryFiniteCalibrationPrepare_value (T P : FairCallSchedule)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (hT : targetAccuracy.value=T.accuracy) (hP : policyAccuracy.value=P.accuracy)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → T.Seed n)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (P.Seed n))
    (N : ℕ) (hN : 0<N) (hs : scale.value=(N:ℚ)) (hl : binaryWordValue last=N-1) :
    let q := countedBinaryFiniteCalibrationPrepare T P mu zlo zhi scale targetAccuracy policyAccuracy last coin
      y seed profiles
    let yQ := fun i j => (y i j).value
    let c := countedCalibrationPrepare mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
      (countedFiniteTargetCall T yQ) (countedFiniteThresholdCall P yQ) yQ seed
      (fun r => binaryCalibrationRankProfileValue (profiles r))
    q.fallback=c.fallback ∧
      q.selected=(if (binaryWordValue coin:ℚ)/(N:ℚ)<rationalMixtureGridRound N hN c.selection.2
        then upperPolicyIndex J c.selection.1 else lowerPolicyIndex J c.selection.1) ∧
      q.active=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<yQ i j))=true) :=
  countedBinaryCalibrationPrepare_value mu zlo zhi scale last coin
    (countedBinaryFiniteTargetCall T y targetAccuracy) (countedFiniteTargetCall T _)
    (fun z b => countedBinaryFiniteTargetCall_value T y targetAccuracy z hT b)
    (countedBinaryFiniteThresholdCall P y policyAccuracy) (countedFiniteThresholdCall P _)
    (countedBinaryFiniteThresholdCall_value P y policyAccuracy hP) y seed profiles N hN hs hl

def finiteBinaryCalibrationTargetHeight (T : FairCallSchedule) (n m Y M : ℕ) : ℕ :=
  finiteFairBankOutputHeight n m Y M 0 (2*M+2) T.bits T.level

def finiteBinaryCalibrationPolicyHeight (P : FairCallSchedule) (n m Y M C D K : ℕ) : ℕ :=
  finiteFairBankOutputHeight n m Y M (7*(C+1)) (3*D+2*K+2) P.bits P.level

/-- A local width for guard, target and validation operations. The scalar
query bounds use only (C,D,K,M,Y), not this enlarged width. -/
def finiteBinaryCalibrationWidth (T P : FairCallSchedule) (n m Y M C D K R : ℕ) : ℕ :=
  4*(M+1)+2+Y+C+D+K+R+(2*M+2)+(3*D+2*K+2)+
    binaryEmpiricalMaximumWidth n (n*m) Y M+(2*n+1)*(3*M+2)+
    finiteBinaryCalibrationTargetHeight T n m Y M+
    finiteBinaryCalibrationPolicyHeight P n m Y M C D K+8

def finiteBinaryCalibrationPrepareWork (T P : FairCallSchedule)
    (n m J Y M C D K R HT HP : ℕ) : ℕ :=
  binaryCalibrationPrepareWork n m J Y M (finiteBinaryCalibrationWidth T P n m Y M C D K R)
    (finiteBinaryCalibrationPolicyHeight P n m Y M C D K)
    (binaryFiniteTargetCallWork T n m Y M (2*M+2) HT)
    (binaryFiniteThresholdCallWork P n m Y M (7*(C+1)) (3*D+2*K+2) HP)

private lemma smallCalibConstants :
    RationalHeight (1/2:ℚ) 3 ∧ RationalHeight (4/5:ℚ) 3 ∧ RationalHeight (1/4:ℚ) 3 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Int.cast_one,Int.cast_ofNat] using
      rationalHeight_of_fraction 1 2 (by decide) 3 (by decide) (by decide)
  · simpa only [Int.cast_ofNat] using
      rationalHeight_of_fraction 4 5 (by decide) 3 (by decide) (by decide)
  · simpa only [Int.cast_one,Int.cast_ofNat] using
      rationalHeight_of_fraction 1 4 (by decide) 3 (by decide) (by decide)

theorem countedBinaryFiniteCalibrationPrepare_work (T P : FairCallSchedule)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → T.Seed n)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (P.Seed n))
    (Y M C D K R HT HP : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (hm : m≤2^M) (hJ : J≤2^K)
    (hmu : RationalHeight mu.value D) (hzlo : RationalHeight zlo.value D)
    (hzhi : RationalHeight zhi.value D) (hscale : RationalHeight scale.value R)
    (hlast : last.length≤R) (hcoin : coin.length≤R)
    (hTa : RationalHeight targetAccuracy.value HT) (hPa : RationalHeight policyAccuracy.value HP)
    (hTime : ∀ r k,RationalHeight ((profiles r).2.2.1 k).value C)
    (hValue : ∀ r k,RationalHeight ((profiles r).2.1 k).value Y) :
    (countedBinaryFiniteCalibrationPrepare T P mu zlo zhi scale targetAccuracy policyAccuracy last coin
      y seed profiles).work≤finiteBinaryCalibrationPrepareWork T P n m J Y M C D K R HT HP := by
  let E := finiteBinaryCalibrationPolicyHeight P n m Y M C D K
  let F := finiteBinaryCalibrationTargetHeight T n m Y M
  let B := finiteBinaryCalibrationWidth T P n m Y M C D K R
  let ZT := 2*M+2
  let ZP := 3*D+2*K+2
  have hCore : 4*(M+1)+2+Y+C+D+K+R+ZT+ZP+binaryEmpiricalMaximumWidth n (n*m) Y M+
      (2*n+1)*(3*M+2)+F+E+8=B := rfl
  have hBasic : M≤B ∧ M+2≤B ∧ K≤B ∧ Y≤B ∧ D≤B ∧ R≤B ∧ 3≤B ∧ C≤B ∧ ZT≤B ∧ ZP≤B ∧ E≤B ∧ F≤B := by
    omega
  obtain ⟨hMB,hM2B,hKB,hYB,hDB,hRB,h3B,hCB,hZTB,hZPB,hEB,hFB⟩ := hBasic
  have hgrid : 4*m≤2^B :=
    (show 4*m≤2^(M+2) by rw [pow_add]; simpa only [show (2:ℕ)^2=4 by decide,Nat.mul_comm] using
      Nat.mul_le_mul_left 4 hm).trans (Nat.pow_le_pow_right (by decide) hM2B)
  have hLen : (m-1).bits.length≤M+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hpow : 0<(2:ℕ)^M := by positivity
    omega
  have hcbar : 4*(m-1).bits.length+2≤2^B :=
    (show 4*(m-1).bits.length+2≤B by omega).trans (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  have hmB := hm.trans (Nat.pow_le_pow_right (by decide) hMB)
  have hJB := hJ.trans (Nat.pow_le_pow_right (by decide) hKB)
  have hStatsM : binaryEmpiricalMaximumWidth n (n*m) Y M≤B := by omega
  have hStatsL : (2*n+1)*(3*M+2)≤B := by omega
  have hmuHalf : RationalHeight (mu.value/2) B :=
    (hmu.div (rationalHeight_natCast 2 1 (by decide))).mono (by omega)
  have hzt (j : TargetGrid m) : RationalHeight ((j.val:ℚ)/(m:ℚ)) ZT :=
    targetGridCoefficient_height M hm j
  have hzp (j : Fin (J+1)) : RationalHeight (storedCalibrationCoefficient J zlo.value zhi.value j.val) ZP :=
    storedCalibrationCoefficient_height J j.val D K _ _ hJ hzlo hzhi
  unfold countedBinaryFiniteCalibrationPrepare finiteBinaryCalibrationPrepareWork
  apply countedBinaryCalibrationPrepare_work _ _ _ _ _ _ _ _ _ _ _
    Y M B E C ZT ZP _ _ hY hm hmB hgrid hJB hcbar (hmu.mono hDB) (hzlo.mono hDB)
    (hzhi.mono hDB) (hscale.mono hRB) (hlast.trans hRB) (hcoin.trans hRB)
    (smallCalibConstants.1.mono h3B) (smallCalibConstants.2.1.mono h3B) (smallCalibConstants.2.2.mono h3B)
    hStatsM hStatsL hmuHalf hzt hzp hTime (fun r k => (hValue r k).mono hYB) hEB hCB hZTB hZPB
  · intro z bits hz
    have hh := countedBinaryFiniteTargetCall_bounds T y targetAccuracy z bits Y M ZT HT hm hY hz
      (by dsimp [ZT]; omega) hTa
    exact ⟨hh.1.mono hFB,hh.2⟩
  · intro A u z bits hu hz
    exact countedBinaryFiniteThresholdCall_bounds P y policyAccuracy A u z bits Y M (7*(C+1)) ZP HP
      hm hY hu hz (by dsimp [ZP]; omega) hPa

def countedBinaryFiniteCalibrationDecision {Obs : Type}
    (P : FairCallSchedule) (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryCalibrationPreparation n m J) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (bits : PolicyQueryArray n J (P.Seed n)) : Bool×ℕ :=
  countedBinaryCalibrationDecision (countedBinaryFiniteThresholdCall P y policyAccuracy) q t x hist i bits

theorem countedBinaryFiniteCalibrationDecision_value {Obs : Type}
    (P : FairCallSchedule) (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryCalibrationPreparation n m J) (zlo zhi : ℚ) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (bits : PolicyQueryArray n J (P.Seed n))
    (hP : policyAccuracy.value=P.accuracy)
    (hCoeff : ∀ k,(q.parameters.coefficient k).value=storedCalibrationCoefficient J zlo zhi k)
    (hActive : q.active=Finset.univ.filter (fun i : Fin n =>
      (List.finRange m).any (fun j => decide (0<(y i j).value))=true)) :
    (countedBinaryFiniteCalibrationDecision P y policyAccuracy q t x hist i bits).1 =
      (countedOnlineCalibrationDecision (storedCalibrationCoefficient J zlo zhi)
        (countedFiniteThresholdCall P (fun i j => (y i j).value)) (fun i j => (y i j).value)
        q.fallback q.selected t.value x.value hist i bits).1 :=
  countedBinaryCalibrationDecision_value _ _ (countedBinaryFiniteThresholdCall_value P y policyAccuracy hP)
    q (fun i j => (y i j).value) zlo zhi t x hist i bits hCoeff hActive

lemma countedBinaryFiniteCalibrationPrepare_coefficient (T P : FairCallSchedule)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → T.Seed n)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (P.Seed n)) :
    ∀ k, ((countedBinaryFiniteCalibrationPrepare T P mu zlo zhi scale targetAccuracy policyAccuracy last coin
      y seed profiles).parameters.coefficient k).value=storedCalibrationCoefficient J zlo.value zhi.value k :=
  (countedBinaryCalibrationPublic_value m J mu zlo zhi).2.2.2.2

def finiteBinaryCalibrationDecisionWork (P : FairCallSchedule)
    (n m J Y M C D K HP : ℕ) : ℕ :=
  binaryCalibrationOnlineWork n J (Y+C+(3*D+2*K+2))
    (finiteBinaryCalibrationPolicyHeight P n m Y M C D K)
    (binaryFiniteThresholdCallWork P n m Y M (7*(C+1)) (3*D+2*K+2) HP)

theorem countedBinaryFiniteCalibrationDecision_work {Obs : Type}
    (P : FairCallSchedule) (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryCalibrationPreparation n m J) (zlo zhi : CalibrationBinary) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (bits : PolicyQueryArray n J (P.Seed n))
    (Y M C D K HP : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (hm : m≤2^M) (hJ : J≤2^K)
    (hlo : RationalHeight zlo.value D) (hhi : RationalHeight zhi.value D)
    (ht : RationalHeight t.value C) (hx : RationalHeight x.value Y) (ha : RationalHeight policyAccuracy.value HP)
    (hCoeff : ∀ k,(q.parameters.coefficient k).value=storedCalibrationCoefficient J zlo.value zhi.value k) :
    (countedBinaryFiniteCalibrationDecision P y policyAccuracy q t x hist i bits).2≤
      finiteBinaryCalibrationDecisionWork P n m J Y M C D K HP := by
  let Z := 3*D+2*K+2
  let B := Y+C+Z
  unfold countedBinaryFiniteCalibrationDecision finiteBinaryCalibrationDecisionWork
  apply countedBinaryCalibrationDecision_work _ q t x hist i bits B
    (finiteBinaryCalibrationPolicyHeight P n m Y M C D K) C Z _ ht (hx.mono (by dsimp [B]; omega))
  · intro j
    rw [hCoeff]
    exact storedCalibrationCoefficient_height J j.val D K _ _ hJ hlo hhi
  · dsimp [B]; omega
  · dsimp [B]; omega
  · intro A u z s hu hz
    exact countedBinaryFiniteThresholdCall_bounds P y policyAccuracy A u z s Y M (7*(C+1)) Z HP
      hm hY hu hz (by dsimp [Z]; omega) ha

/-- This executable version receives the two confidence indices already
computed during public setup. -/
def countedBinaryFiniteCalibrationPrepareAt (tb tr ta pb pr pa : ℕ)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → FairQueryBank n tb (2*ta+1) tr)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (FairQueryBank n pb (2*pa+1) pr)) :
    BinaryCalibrationPreparation n m J :=
  countedBinaryCalibrationPrepare mu zlo zhi scale last coin
    (countedBinaryFiniteTargetCallAt tb tr ta y targetAccuracy)
    (countedBinaryFiniteThresholdCallAt pb pr pa y policyAccuracy) y seed profiles

def countedBinaryFiniteCalibrationDecisionAt {Obs : Type} (b R a : ℕ)
    (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryCalibrationPreparation n m J) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n)
    (bits : PolicyQueryArray n J (FairQueryBank n b (2*a+1) R)) : Bool×ℕ :=
  countedBinaryCalibrationDecision (countedBinaryFiniteThresholdCallAt b R a y policyAccuracy) q t x hist i bits

/-- Retyping the two finite banks uses only the equality of their public
confidence indices. No search is performed by this adapter. -/
def countedBinaryFiniteCalibrationPrepareCached (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(Probability.countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(Probability.countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → T.Seed n)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (P.Seed n)) :
    BinaryCalibrationPreparation n m J :=
  countedBinaryFiniteCalibrationPrepareAt T.bits T.level ta P.bits P.level pa
    mu zlo zhi scale targetAccuracy policyAccuracy last coin y
    (fun k => cast (by rw [ht]; rfl) (seed k)) (fun k =>
      let d := profiles k
      (d.1,d.2.1,d.2.2.1,fun j => cast (by rw [hp]; rfl) (d.2.2.2 j)))

theorem countedBinaryFiniteCalibrationPrepareCached_eq (T P : FairCallSchedule) (ta pa : ℕ)
    (ht : ta=(Probability.countedConfidenceLevel T.failure T.confidence).1)
    (hp : pa=(Probability.countedConfidenceLevel P.failure P.confidence).1)
    (mu zlo zhi scale targetAccuracy policyAccuracy : CalibrationBinary) (last coin : List Bool)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → T.Seed n)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary (P.Seed n)) :
    countedBinaryFiniteCalibrationPrepareCached T P ta pa ht hp mu zlo zhi scale targetAccuracy policyAccuracy
      last coin y seed profiles =
    countedBinaryFiniteCalibrationPrepare T P mu zlo zhi scale targetAccuracy policyAccuracy last coin y seed profiles := by
  subst ta
  subst pa
  rfl

def countedBinaryFiniteCalibrationDecisionCached {Obs : Type} (P : FairCallSchedule) (a : ℕ)
    (ha : a=(Probability.countedConfidenceLevel P.failure P.confidence).1)
    (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryCalibrationPreparation n m J) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (bits : PolicyQueryArray n J (P.Seed n)) : Bool×ℕ :=
  countedBinaryFiniteCalibrationDecisionAt P.bits P.level a y policyAccuracy q t x hist i
    (fun k => cast (by rw [ha]; rfl) (bits k))

theorem countedBinaryFiniteCalibrationDecisionCached_eq {Obs : Type} (P : FairCallSchedule) (a : ℕ)
    (ha : a=(Probability.countedConfidenceLevel P.failure P.confidence).1)
    (y : Fin n → Fin m → CalibrationBinary) (policyAccuracy : CalibrationBinary)
    (q : BinaryCalibrationPreparation n m J) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (bits : PolicyQueryArray n J (P.Seed n)) :
    countedBinaryFiniteCalibrationDecisionCached P a ha y policyAccuracy q t x hist i bits =
      countedBinaryFiniteCalibrationDecision P y policyAccuracy q t x hist i bits := by
  subst a
  rfl

end ProphetSecretary.Statistics.Calibration
