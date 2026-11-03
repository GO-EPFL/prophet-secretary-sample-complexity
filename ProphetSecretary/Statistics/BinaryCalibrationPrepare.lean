import ProphetSecretary.Statistics.BinaryCalibrationPublic
import ProphetSecretary.Statistics.BinaryCalibrationKnots
import ProphetSecretary.Statistics.BinaryCalibrationOnline

/-!
# Binary calibration preparation

Training statistics, public grids and validation trajectories are
materialized in that order. Online execution reuses the stored active
set and chosen coefficient.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {n m J : ℕ} {TSeed PSeed : Type}

structure BinaryCalibrationPreparation (n m J : ℕ) where
  parameters : BinaryCalibrationPublic m J
  active : Finset (Fin n)
  selected : Fin (J+1)
  fallback : Bool
  work : ℕ

def countedBinaryCalibrationPrepare (mu zlo zhi scale : CalibrationBinary) (last coin : List Bool)
    (target : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → TSeed)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary PSeed) :
    BinaryCalibrationPreparation n m J :=
  let p := countedBinaryCalibrationPublic m J mu zlo zhi
  let t := countedBinaryTrainingStatistics y
  let f := countedBinaryFallback t.positiveCount t.maximum p.Lbar (BinaryRational.ofRat (1/4))
  let rho := countedBinaryTargetMinimum p.muHalf t.positiveCount t.maximum p.Lbar p.invM
    (BinaryRational.ofRat (1/2)) (BinaryRational.ofRat (4/5)) p.targetGrid.get target seed
  let durations : Vector (Array CalibrationBinary×ℕ) m := Vector.ofFn fun r =>
    let d := profiles r
    countedBinaryRankValidationMemo p.coefficient estimate t.active f.1 d.1 d.2.1 d.2.2.1 d.2.2.2
  let q := countedBinaryCalibrationSelection p.invM rho.1 scale last coin (fun r => (durations.get r).1) J
  ⟨p,t.active,q.selected,f.1,p.work+t.work+f.2+rho.2+
    (∑ r : Fin m,((durations.get r).2+2))+q.work+8⟩

def binaryCalibrationRankProfileValue (d : CalibrationRankProfile n J CalibrationBinary PSeed) :
    CalibrationRankProfile n J ℚ PSeed :=
  (d.1,((fun i => (d.2.1 i).value),((fun i => (d.2.2.1 i).value),d.2.2.2)))

lemma binaryCalibrationActive_rank {q : Fin n → Fin m → ℚ} {A : Finset (Fin n)}
    (hA : A=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<q i j))=true))
    (p : Equiv.Perm (Fin n)) (k : Fin n) :
    A.filter (fun i => k<p.symm i)=rankContinuationSet q p k := by
  ext i
  simp [hA,rankContinuationSet,and_comm]

lemma binaryCalibrationActive_online {q : Fin n → Fin m → ℚ} {A : Finset (Fin n)} {Obs : Type}
    (hA : A=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<q i j))=true))
    (hist : Fin n → Option Obs) (k : Fin n) :
    A.filter (fun i => i≠k ∧ (hist i).isNone=true)=onlineContinuationSet q hist k := by
  ext i
  simp [hA,onlineContinuationSet,and_comm,and_assoc]

theorem countedBinaryCalibrationPrepare_value (mu zlo zhi scale : CalibrationBinary) (last coin : List Bool)
    (target : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (targetQ : ℚ → TSeed → ℚ×ℕ) (ht : ∀ z r,(target z r).1.value=(targetQ z.value r).1)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (estimateQ : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ×ℕ)
    (he : ∀ A u z r,(estimate A u z r).1.value=(estimateQ A u.value z.value r).1)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → TSeed)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary PSeed)
    (N : ℕ) (hN : 0<N) (hs : scale.value=(N:ℚ)) (hl : binaryWordValue last=N-1) :
    let q := countedBinaryCalibrationPrepare mu zlo zhi scale last coin target estimate y seed profiles
    let yQ := fun i j => (y i j).value
    let c := countedCalibrationPrepare mu.value zlo.value zhi.value (4*(Nat.clog 2 m:ℚ)+2)
      targetQ estimateQ yQ seed (fun r => binaryCalibrationRankProfileValue (profiles r))
    q.fallback=c.fallback ∧
      q.selected=(if (binaryWordValue coin:ℚ)/(N:ℚ)<rationalMixtureGridRound N hN c.selection.2
        then upperPolicyIndex J c.selection.1 else lowerPolicyIndex J c.selection.1) ∧
      q.active=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<yQ i j))=true) := by
  let yQ := fun i j => (y i j).value
  let p := countedBinaryCalibrationPublic m J mu zlo zhi
  let t := countedBinaryTrainingStatistics y
  let Lbar : ℚ := 4*(Nat.clog 2 m:ℚ)+2
  let M := countedEmpiricalMaximum (empiricalStoredRows yQ)
  let L : ℚ := ∑ i : Fin n,plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows yQ)).1 i
  let f := countedBinaryFallback t.positiveCount t.maximum p.Lbar (BinaryRational.ofRat (1/4))
  let rho := countedBinaryTargetMinimum p.muHalf t.positiveCount t.maximum p.Lbar p.invM
    (BinaryRational.ofRat (1/2)) (BinaryRational.ofRat (4/5)) p.targetGrid.get target seed
  have hP := countedBinaryCalibrationPublic_value m J mu zlo zhi
  have hT := countedBinaryTrainingStatistics_value y
  have hf : f.1=decide (Lbar<L ∨ 1/4<M.1) := by
    change (countedBinaryFallback t.positiveCount t.maximum p.Lbar (BinaryRational.ofRat (1/4))).1=_
    rw [countedBinaryFallback_value,BinaryRational.ofRat_value,hP.2.2.1,hT.1,hT.2.1]
  have hrho : rho.1.value=(countedTargetMinimum mu.value L M.1 Lbar targetQ seed).1 := by
    have hr := countedBinaryTargetMinimum_value p.muHalf t.positiveCount t.maximum p.Lbar p.invM
      (BinaryRational.ofRat (1/2)) (BinaryRational.ofRat (4/5)) p.targetGrid.get target targetQ ht
      seed mu.value hP.2.1 (hP.1.trans (one_div _).symm) (BinaryRational.ofRat_value _) (BinaryRational.ofRat_value _) hP.2.2.2.1
    change rho.1.value=_ at hr
    rw [hP.2.2.1,hT.1,hT.2.1] at hr
    exact hr
  let d := fun r : Fin m =>
    let v := profiles r
    (countedBinaryRankValidationMemo p.coefficient estimate t.active f.1 v.1 v.2.1 v.2.2.1 v.2.2.2).1
  let D := fun r : Fin m =>
    let v := binaryCalibrationRankProfileValue (profiles r)
    (countedRankValidationMemo (storedCalibrationCoefficient J zlo.value zhi.value)
      estimateQ yQ (decide (Lbar<L ∨ 1/4<M.1)) v.1 v.2.1 v.2.2.1 v.2.2.2).1
  have hd : (fun r => (d r).map BinaryRational.value)=D := by
    funext r
    let v := profiles r
    have hh := countedBinaryRankValidationMemo_value p.coefficient estimate estimateQ he yQ t.active
      f.1 v.1 v.2.1 v.2.2.1 v.2.2.2 (fun k => binaryCalibrationActive_rank hT.2.2 v.1 k)
    rw [show (fun l => (p.coefficient l).value)=storedCalibrationCoefficient J zlo.value zhi.value
      from funext hP.2.2.2.2,hf] at hh
    simpa only [d,D,v,binaryCalibrationRankProfileValue,hf] using hh
  have hS := (countedBinaryCalibrationSelection_value p.invM rho.1 scale last coin d J N hN hP.1 hs hl).2.2
  rw [hd,hrho] at hS
  refine ⟨hf,?_,hT.2.2⟩
  unfold countedBinaryCalibrationPrepare countedCalibrationPrepare
  simp only [calibrationVectorGet_ofFn]
  exact hS

def countedBinaryCalibrationDecision {Obs : Type}
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (q : BinaryCalibrationPreparation n m J) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed) : Bool×ℕ :=
  countedBinaryOnlineCalibration q.parameters.coefficient estimate q.active q.fallback q.selected t x hist i r

private lemma targetScan_height (M invM low high : CalibrationBinary)
    (calls : List (CalibrationBinary×(CalibrationBinary×ℕ))) (B : ℕ)
    (hM : RationalHeight M.value B) (hi : RationalHeight invM.value B)
    (hlo : RationalHeight low.value B) (hhi : RationalHeight high.value B)
    (h : ∀ c∈calls,RationalHeight c.1.value B ∧ RationalHeight c.2.1.value B) :
    RationalHeight (countedBinaryTargetScan M invM low high calls).1.value (7*(B+1)) := by
  let A := 7*(B+1)
  have hBA : B≤A := by dsimp [A]; omega
  let l := calls.map (fun c =>
    let r := (binaryTargetRatio M c.1 c.2.1 invM).evaluate
    (r.1,c.2.2+r.2+1))
  have hl : ∀ a∈l,RationalHeight a.1.value A := by
    intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    have hh := h c hc
    change RationalHeight (binaryTargetRatio M c.1 c.2.1 invM).evaluate.1.value (7*(B+1))
    exact binaryTargetRatio_height M _ _ _ B hM hh.1 hh.2 hi
  have hMin := countedBinaryMinScan_height high l A (hhi.mono hBA) hl
  change RationalHeight (BinaryRational.countedOperation .maximum low (countedBinaryMinScan high l).1).1.value A
  rw [countedCalibrationOp_value]
  exact ((hlo.mono hBA).max hMin).mono (max_le le_rfl le_rfl)

private lemma targetMinimum_height (muHalf L M Lbar invM low high : CalibrationBinary)
    (grid : TargetGrid m → CalibrationBinary) (estimate : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (seed : TargetGrid m → TSeed) (B : ℕ)
    (hM : RationalHeight M.value B) (hi : RationalHeight invM.value B)
    (hlo : RationalHeight low.value B) (hhi : RationalHeight high.value B)
    (h : ∀ j,RationalHeight (grid j).value B ∧ RationalHeight (estimate (grid j) (seed j)).1.value B) :
    RationalHeight (countedBinaryTargetMinimum muHalf L M Lbar invM low high grid estimate seed).1.value
      (7*(B+1)) := by
  unfold countedBinaryTargetMinimum
  dsimp only
  split_ifs
  · apply targetScan_height _ _ _ _ _ B hM hi hlo hhi
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact h j
  · exact hhi.mono (by omega)

private lemma durationScan_height {a : Type} (test : a→Bool×ℕ) (clock : a→CalibrationBinary)
    (l : List a) (B : ℕ) (h : ∀ k,RationalHeight (clock k).value B) :
    RationalHeight (countedBinaryDurationScan test clock l).1.value B := by
  induction l with
  | nil =>
    change RationalHeight (1:CalibrationBinary).value B
    rw [BinaryRational.one_value]
    exact rationalHeight_one.mono (Nat.zero_le _)
  | cons a l ih =>
    rw [countedBinaryDurationScan]
    dsimp only
    split_ifs
    · exact h a
    · exact ih

private lemma validationMemo_duration_height (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (fallback : Bool) (p : Equiv.Perm (Fin n))
    (x s : Fin n → CalibrationBinary) (r : PolicyQueryArray n J PSeed) (j B : ℕ)
    (hs : ∀ k,RationalHeight (s k).value B) :
    RationalHeight (((countedBinaryRankValidationMemo z estimate active fallback p x s r).1[j]?).getD 1 :
      CalibrationBinary).value B := by
  unfold countedBinaryRankValidationMemo
  dsimp only
  rw [Array.map_ofFn]
  by_cases hj : j<J+1
  · rw [Array.getElem?_ofFn,dif_pos hj,Option.getD_some]
    exact durationScan_height _ _ _ B hs
  · rw [Array.getElem?_ofFn,dif_neg hj,Option.getD_none,BinaryRational.one_value]
    exact rationalHeight_one.mono (Nat.zero_le _)

def binaryCalibrationValidationWork (n J B E W : ℕ) : ℕ :=
  n*(n+7*CalibrationBinaryExpr.workUnit 7 B+(J+1)*(W+3600*(E+2)^3+3)+6)+
    (J+1)*(3+n*(binaryRankAcceptWork B+2))+2

/-- The component bounds are in the public dimensions, the input widths
and the work and output widths of the two counted query algorithms. -/
def binaryCalibrationPrepareWork (n m J Y P B E WT WP : ℕ) : ℕ :=
  binaryCalibrationPublicWork m J B+binaryTrainingStatisticsWork n m Y P+
    (2*calibrationComparisonWork B+2)+
    (2*calibrationComparisonWork B+binaryTargetScanWork (4*m+1) B WT+3)+
    m*(binaryCalibrationValidationWork n J B E WP+2)+
    binaryCalibrationSelectionWork m J (7*(B+1))+8

theorem countedBinaryCalibrationPrepare_work (mu zlo zhi scale : CalibrationBinary) (last coin : List Bool)
    (target : CalibrationBinary → TSeed → CalibrationBinary×ℕ)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (y : Fin n → Fin m → CalibrationBinary) (seed : TargetGrid m → TSeed)
    (profiles : Fin m → CalibrationRankProfile n J CalibrationBinary PSeed)
    (Y P B E T ZT ZP WT WP : ℕ)
    (hY : ∀ i j,RationalHeight (y i j).value Y) (hP : m≤2^P)
    (hm : m≤2^B) (hgrid : 4*m≤2^B) (hJ : J≤2^B) (hcbar : 4*(m-1).bits.length+2≤2^B)
    (hmu : RationalHeight mu.value B) (hzlo : RationalHeight zlo.value B)
    (hzhi : RationalHeight zhi.value B) (hscale : RationalHeight scale.value B)
    (hlast : last.length≤B) (hcoin : coin.length≤B)
    (hhalf : RationalHeight (1/2) B) (hfour : RationalHeight (4/5) B) (hquarter : RationalHeight (1/4) B)
    (hM : binaryEmpiricalMaximumWidth n (n*m) Y P≤B)
    (hL : (2*n+1)*(3*P+2)≤B)
    (hmuHalf : RationalHeight (mu.value/2) B)
    (hTargetGrid : ∀ j : TargetGrid m,RationalHeight ((j.val:ℚ)/(m:ℚ)) ZT)
    (hCoeff : ∀ j : Fin (J+1),RationalHeight (storedCalibrationCoefficient J zlo.value zhi.value j.val) ZP)
    (hTime : ∀ r k,RationalHeight ((profiles r).2.2.1 k).value T)
    (hValue : ∀ r k,RationalHeight ((profiles r).2.1 k).value B)
    (hEB : E≤B) (hTB : T≤B) (hZTB : ZT≤B) (hZPB : ZP≤B)
    (hTarget : ∀ z r,RationalHeight z.value ZT →
      RationalHeight (target z r).1.value B ∧ (target z r).2≤WT)
    (hEstimate : ∀ A u z r,RationalHeight u.value (7*(T+1)) → RationalHeight z.value ZP →
      RationalHeight (estimate A u z r).1.value E ∧ (estimate A u z r).2≤WP) :
    (countedBinaryCalibrationPrepare mu zlo zhi scale last coin target estimate y seed profiles).work≤
      binaryCalibrationPrepareWork n m J Y P B E WT WP := by
  let p := countedBinaryCalibrationPublic m J mu zlo zhi
  let t := countedBinaryTrainingStatistics y
  let quarter := BinaryRational.ofRat (1/4)
  let low := BinaryRational.ofRat (1/2)
  let high := BinaryRational.ofRat (4/5)
  let f := countedBinaryFallback t.positiveCount t.maximum p.Lbar quarter
  let rho := countedBinaryTargetMinimum p.muHalf t.positiveCount t.maximum p.Lbar p.invM low high
    p.targetGrid.get target seed
  have hp := countedBinaryCalibrationPublic_work m J mu zlo zhi B hm hgrid hJ hcbar hmu hzlo hzhi hhalf
  have ht := countedBinaryTrainingStatistics_work y Y P hY hP
  have htH := countedBinaryTrainingStatistics_height y Y P hY hP
  have hMH : RationalHeight t.maximum.value B := htH.1.mono hM
  have hLH : RationalHeight t.positiveCount.value B := htH.2.mono hL
  have hpV := countedBinaryCalibrationPublic_value m J mu zlo zhi
  have hI : RationalHeight p.invM.value B := by
    rw [hpV.1,←one_div]
    exact (rationalHeight_one.div (rationalHeight_natCast _ _ hm)).mono (by omega)
  have hU : RationalHeight p.muHalf.value B := by rw [hpV.2.1]; exact hmuHalf
  have hB : RationalHeight p.Lbar.value B := by
    rw [hpV.2.2.1]
    have hh := rationalHeight_natCast (4*(m-1).bits.length+2) B hcbar
    simpa only [←calibrationClog_eq_width,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hLo : RationalHeight low.value B := by simpa only [low,BinaryRational.ofRat_value] using hhalf
  have hHi : RationalHeight high.value B := by simpa only [high,BinaryRational.ofRat_value] using hfour
  have hQ : RationalHeight quarter.value B := by simpa only [quarter,BinaryRational.ofRat_value] using hquarter
  have hf : f.2≤2*calibrationComparisonWork B+2 := by
    have ha := countedCalibrationLT_work p.Lbar t.positiveCount B hB hLH
    have hb := countedCalibrationLT_work quarter t.maximum B hQ hMH
    change (countedCalibrationLT p.Lbar t.positiveCount).2+(countedCalibrationLT quarter t.maximum).2+2≤_
    omega
  have hg (j : TargetGrid m) : RationalHeight (p.targetGrid.get j).value ZT := by
    rw [hpV.2.2.2.1]
    exact hTargetGrid j
  have hz (j : Fin (J+1)) : RationalHeight (p.coefficient j.val).value ZP := by
    rw [hpV.2.2.2.2]
    exact hCoeff j
  have hrho := countedBinaryTargetMinimum_work p.muHalf t.positiveCount t.maximum p.Lbar p.invM low high
    p.targetGrid.get target seed B WT hU hLH hMH hB hI hLo hHi
    (fun j => ⟨(hg j).mono hZTB,hTarget _ _ (hg j)⟩)
  have hrhoH := targetMinimum_height p.muHalf t.positiveCount t.maximum p.Lbar p.invM low high
    p.targetGrid.get target seed B hMH hI hLo hHi (fun j => ⟨(hg j).mono hZTB,(hTarget _ _ (hg j)).1⟩)
  let d := fun r : Fin m =>
    let v := profiles r
    countedBinaryRankValidationMemo p.coefficient estimate t.active f.1 v.1 v.2.1 v.2.2.1 v.2.2.2
  have hD (r : Fin m) : (d r).2≤binaryCalibrationValidationWork n J B E WP := by
    let v := profiles r
    refine countedBinaryRankValidationMemo_work p.coefficient estimate t.active f.1
      v.1 v.2.1 v.2.2.1 v.2.2.2 B E WP (fun j => (hz j).mono hZPB)
      (fun k => (hTime r k).mono hTB) (hValue r) hEB ?_
    intro k l hl
    apply hEstimate _ _ _ _
    · rw [CalibrationBinaryExpr.evaluate_value]
      exact (binaryRemainingHorizon (v.2.2.1 k)).value_height T
        (binaryRemainingHorizon_leaves _ _ (hTime r k))
    · exact hz ⟨l,by omega⟩
  have hDS : (∑ r : Fin m,((d r).2+2))≤m*(binaryCalibrationValidationWork n J B E WP+2) := by
    have hh := Finset.sum_le_sum (fun r (_ : r∈Finset.univ) => Nat.add_le_add_right (hD r) 2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hh
  let A := 7*(B+1)
  have hBA : B≤A := by dsimp [A]; omega
  have hK := countedBinaryCalibrationSelection_work p.invM rho.1 scale last coin
    (fun r => (d r).1) J A (hI.mono hBA) hrhoH (hscale.mono hBA) (hlast.trans hBA) (hcoin.trans hBA)
    (fun r j => validationMemo_duration_height p.coefficient estimate t.active f.1
      (profiles r).1 (profiles r).2.1 (profiles r).2.2.1 (profiles r).2.2.2 j A
      (fun k => (hTime r k).mono (hTB.trans hBA)))
  unfold countedBinaryCalibrationPrepare
  simp only [calibrationVectorGet_ofFn]
  change p.work+t.work+f.2+rho.2+(∑ r : Fin m,((d r).2+2))+
    (countedBinaryCalibrationSelection p.invM rho.1 scale last coin (fun r => (d r).1) J).work+8≤_
  change p.work≤_ at hp
  change t.work≤_ at ht
  change rho.2≤_ at hrho
  unfold binaryCalibrationPrepareWork
  change _≤binaryCalibrationPublicWork m J B+binaryTrainingStatisticsWork n m Y P+
    (2*calibrationComparisonWork B+2)+
    (2*calibrationComparisonWork B+binaryTargetScanWork (4*m+1) B WT+3)+
    m*(binaryCalibrationValidationWork n J B E WP+2)+binaryCalibrationSelectionWork m J A+8
  omega

theorem countedBinaryCalibrationDecision_value {Obs : Type}
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (estimateQ : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ×ℕ)
    (he : ∀ A u z r,(estimate A u z r).1.value=(estimateQ A u.value z.value r).1)
    (q : BinaryCalibrationPreparation n m J) (rows : Fin n → Fin m → ℚ) (zlo zhi : ℚ)
    (t x : CalibrationBinary) (hist : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed)
    (hCoeff : ∀ j,(q.parameters.coefficient j).value=storedCalibrationCoefficient J zlo zhi j)
    (hActive : q.active=Finset.univ.filter (fun i : Fin n =>
        (List.finRange m).any (fun j => decide (0<rows i j))=true)) :
    (countedBinaryCalibrationDecision estimate q t x hist i r).1 =
      (countedOnlineCalibrationDecision (storedCalibrationCoefficient J zlo zhi)
        estimateQ rows q.fallback q.selected t.value x.value hist i r).1 := by
  unfold countedBinaryCalibrationDecision
  rw [countedBinaryOnlineCalibration_value q.parameters.coefficient estimate estimateQ he rows q.active
    q.fallback q.selected t x hist i r (binaryCalibrationActive_online hActive hist i),funext hCoeff]

theorem countedBinaryCalibrationDecision_work {Obs : Type}
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (q : BinaryCalibrationPreparation n m J) (t x : CalibrationBinary)
    (hist : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed)
    (B E T Z W : ℕ) (ht : RationalHeight t.value T) (hx : RationalHeight x.value B)
    (hz : ∀ j : Fin (J+1),RationalHeight (q.parameters.coefficient j.val).value Z)
    (hTB : T≤B) (hZB : Z≤B)
    (hEstimate : ∀ A u z r,RationalHeight u.value (7*(T+1)) → RationalHeight z.value Z →
      RationalHeight (estimate A u z r).1.value E ∧ (estimate A u z r).2≤W) :
    (countedBinaryCalibrationDecision estimate q t x hist i r).2≤binaryCalibrationOnlineWork n J B E W := by
  unfold countedBinaryCalibrationDecision
  apply countedBinaryOnlineCalibration_work _ _ _ _ _ _ _ _ _ _ B E W (ht.mono hTB) hx ((hz q.selected).mono hZB)
  intro l hl
  apply hEstimate _ _ _ _
  · rw [CalibrationBinaryExpr.evaluate_value]
    exact (binaryRemainingHorizon t).value_height T (binaryRemainingHorizon_leaves _ _ ht)
  · exact hz ⟨l,by have := q.selected.isLt; omega⟩

end ProphetSecretary.Statistics.Calibration
