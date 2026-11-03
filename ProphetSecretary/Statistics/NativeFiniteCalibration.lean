import ProphetSecretary.Statistics.FiniteBitWork
import ProphetSecretary.Statistics.NativeCalibrationDecision

/-!
# Correspondence of the scheduled native rank procedure

The counted preparation decodes the finite arrays once and retains the
selected policy index, empirical guard and assigned timestamps. On a
legal rank prefix the counted online procedure makes exactly the measured
rank decision at the current assigned timestamp.
-/

open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ}

theorem countedFiniteCalibrationDecision_eq [NeZero m]
    (P : FairCallSchedule) (zlo zhi : ℚ)
    (estimate : ContinuationEstimator n m (P.Seed n))
    (workR : Finset (Fin n) → ℝ → ℝ → P.Seed n → ℕ)
    (q : FiniteCalibrationPreparation n m J (P.Seed n))
    (hGuard : q.fallback=decide (familyFallback (calibrationRowsCast q.rows)))
    (hEst : ∀ A u z r, ((countedFiniteThresholdCall P q.rows A u z r).1 : ℝ)=
      estimate (calibrationRowsCast q.rows) A (u : ℝ) (z : ℝ) r)
    (k i : Fin n) (x : ℚ) (H : Fin n → Option (Fin n × ℚ))
    (hRank : onlineQueryRank H i=k) :
    (countedFiniteCalibrationDecision P zlo zhi q i x H).1 =
      (numericalFamilyPolicy (zlo : ℝ) (zhi : ℝ) estimate q.selected).clockToRank.decide
        ((fun i => (q.clocks i : ℝ)),calibrationRowsCast q.rows,q.queryBits)
        k i (x : ℝ) (calibrationRankHistoryCast H) :=
  countedOnlineCalibrationNativeRank_eq zlo zhi (countedFiniteThresholdCall P q.rows)
    estimate workR q.rows q.fallback hGuard hEst q.queryBits q.selected q.clocks k i x H hRank

/-- The native selected coefficient includes the same rounded independent coin. -/
theorem countedFiniteCalibrationPrepare_data_eq [NeZero m]
    (T P : FairCallSchedule) (b c : ℕ) (mu zlo zhi Lbar : ℚ)
    (hLbar : (Lbar : ℝ)=targetCountCutoff m)
    (y : Fin n → Fin m → ℚ) (x : Fin m → Fin n → ℚ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (target : TargetEstimator n m (T.Seed n)) (estimate : ContinuationEstimator n m (P.Seed n))
    (ht : ∀ z s, ((countedFiniteTargetCall T y z s).1 : ℝ)=target (calibrationRowsCast y) (z : ℝ) s)
    (he : ∀ A u z s, ((countedFiniteThresholdCall P y A u z s).1 : ℝ)=
      estimate (calibrationRowsCast y) A (u : ℝ) (z : ℝ) s) :
    let q := countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar y x bits
    let d := interpretRankCalibrationBits b c bits
    let a := rankValidationPrepare (J := J) (mu : ℝ) (zlo : ℝ) (zhi : ℝ) target estimate
      ((reservoirCoordinates (calibrationRowsCast y),d.1),
        fun j => ((fun i => (x j i : ℝ)),d.2.1 j))
    let α := ProphetSecretary.Probability.uniformGridRound (2^c) (by positivity) a.2.2
    q.rows=y ∧ q.fallback=decide (familyFallback (calibrationRowsCast y)) ∧
      q.selected=mixturePolicyIndex J (a.2.1,α) d.2.2.2.2 ∧
      (fun i => (q.clocks i : ℝ))=d.2.2.1 ∧ q.queryBits=d.2.2.2.1 := by
  let d := (countedDecodeRankCalibrationBits b c bits).1
  let dR := rationalRankCalibratedSeedCast d
  let pf := fun j : Fin m => ((d.2.1 j).1,x j,(d.2.1 j).2.1,(d.2.1 j).2.2)
  let q := countedCalibrationPrepare mu zlo zhi Lbar (countedFiniteTargetCall T y)
    (countedFiniteThresholdCall P y) y d.1 pf
  let qR := countedCalibrationPrepare (mu : ℝ) (zlo : ℝ) (zhi : ℝ) (Lbar : ℝ)
    (fun z s => (target (calibrationRowsCast y) z s,0))
    (fun A u z s => (estimate (calibrationRowsCast y) A u z s,0))
    (calibrationRowsCast y) d.1 (fun j => calibrationProfileCast (pf j))
  have hCast : qR.rows=calibrationRowsCast q.rows ∧ qR.fallback=q.fallback ∧
      qR.selection=(q.selection.1,(q.selection.2 : ℝ)) :=
    countedCalibrationPrepare_ratCast mu zlo zhi Lbar _ _ _ _ ht he y d.1 pf
  let a := rankValidationPrepare (J := J) (mu : ℝ) (zlo : ℝ) (zhi : ℝ) target estimate
    ((reservoirCoordinates (calibrationRowsCast y),dR.1),fun j => ((fun i => (x j i : ℝ)),dR.2.1 j))
  have hSel : (qR.rows,qR.selection)=a ∧ qR.fallback=decide (familyFallback (calibrationRowsCast y)) := by
    unfold qR
    rw [hLbar]
    exact countedCalibrationPrepare_eq_rankValidationPrepare (mu : ℝ) (zlo : ℝ) (zhi : ℝ)
      target (fun _ _ => 0) estimate (fun _ _ _ _ => 0) (calibrationRowsCast y) d.1
      (fun j => calibrationProfileCast (pf j))
  have hPoint : (q.selection.1,(q.selection.2 : ℝ))=a.2 :=
    hCast.2.2.symm.trans (congrArg Prod.snd hSel.1)
  have hD : dR=interpretRankCalibrationBits b c bits := countedDecodeRankCalibrationBits_value b c bits
  dsimp only
  rw [← hD]
  change q.rows=y ∧ q.fallback=decide (familyFallback (calibrationRowsCast y)) ∧
    rationalMixturePolicyIndex J q.selection.1
      (rationalMixtureGridRound (countedBitGridSize c).1 (by rw [countedBitGridSize_value]; positivity) q.selection.2)
      d.2.2.2.2 =
        mixturePolicyIndex J (a.2.1,ProphetSecretary.Probability.uniformGridRound (2^c) (by positivity) a.2.2)
          (d.2.2.2.2 : ℝ) ∧
    (fun i => (d.2.2.1 i : ℝ))=dR.2.2.1 ∧ d.2.2.2.1=dR.2.2.2.1
  refine ⟨rfl,hCast.2.1.symm.trans hSel.2,?_,rfl,rfl⟩
  rw [rationalMixturePolicyIndex_eq,rationalMixtureGridRound_cast]
  have h1 : q.selection.1=a.2.1 := congrArg Prod.fst hPoint
  have h2 : (q.selection.2 : ℝ)=a.2.2 := congrArg Prod.snd hPoint
  have hRound (N : ℕ) (hN : 0<N) (hN' : N=2^c) :
      ProphetSecretary.Probability.uniformGridRound N hN (q.selection.2 : ℝ) =
        ProphetSecretary.Probability.uniformGridRound (2^c) (by positivity) a.2.2 := by
    subst N
    rw [h2]
  rw [h1,hRound _ _ (countedBitGridSize_value c)]


def rationalCalibrationFirstBlock (data : Fin n → Fin (2*m) → ℚ) : Fin n → Fin m → ℚ :=
  fun i j => data i (blockIndex (.inl (i,j))).2

def rationalCalibrationValidationValues (data : Fin n → Fin (2*m) → ℚ) : Fin m → Fin n → ℚ :=
  fun j i => data i (blockIndex (.inr (i,j))).2

/-- The complete native preparation and online decision realize the measured
finite-bit sample policy on rational inputs and a legal observed prefix. -/
theorem countedFiniteCalibrationExecution_eq [NeZero m]
    (T P : FairCallSchedule) (b c : ℕ) (mu zlo zhi Lbar : ℚ)
    (hLbar : (Lbar : ℝ)=targetCountCutoff m)
    (data : Fin n → Fin (2*m) → ℚ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n))
    (target : TargetEstimator n m (T.Seed n)) (estimate : ContinuationEstimator n m (P.Seed n))
    (ht : ∀ z s, ((countedFiniteTargetCall T (rationalCalibrationFirstBlock data) z s).1 : ℝ)=
      target (calibrationRowsCast (rationalCalibrationFirstBlock data)) (z : ℝ) s)
    (he : ∀ A u z s, ((countedFiniteThresholdCall P (rationalCalibrationFirstBlock data) A u z s).1 : ℝ)=
      estimate (calibrationRowsCast (rationalCalibrationFirstBlock data)) A (u : ℝ) (z : ℝ) s)
    (k i : Fin n) (value : ℚ) (H : Fin n → Option (Fin n × ℚ))
    (hRank : onlineQueryRank H i=k) :
    let q := countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
      (rationalCalibrationFirstBlock data) (rationalCalibrationValidationValues data) bits
    (countedFiniteCalibrationDecision P zlo zhi q i value H).1 =
      (rankCalibratedSamplePolicy (J := J) (ProphetSecretary.Probability.uniformGridRound (2^c) (by positivity))
        (mu : ℝ) (zlo : ℝ) (zhi : ℝ) target estimate).decide
        ((fun i j => (data i j : ℝ)),interpretRankCalibrationBits b c bits)
        k i (value : ℝ) (calibrationRankHistoryCast H) := by
  let y := rationalCalibrationFirstBlock data
  let x := rationalCalibrationValidationValues data
  let q := countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar y x bits
  let d := interpretRankCalibrationBits b c bits
  let a := rankValidationPrepare (J := J) (mu : ℝ) (zlo : ℝ) (zhi : ℝ) target estimate
    ((reservoirCoordinates (calibrationRowsCast y),d.1),
      fun j => ((fun i => (x j i : ℝ)),d.2.1 j))
  obtain ⟨hRows,hGuard,hSelected,hTimes,hSeed⟩ :=
    countedFiniteCalibrationPrepare_data_eq T P b c mu zlo zhi Lbar hLbar y x bits target estimate ht he
  have hG : q.fallback=decide (familyFallback (calibrationRowsCast q.rows)) := by
    rw [hRows]
    exact hGuard
  have hE (A : Finset (Fin n)) (u z : ℚ) (s : P.Seed n) :
      ((countedFiniteThresholdCall P q.rows A u z s).1 : ℝ)=
        estimate (calibrationRowsCast q.rows) A (u : ℝ) (z : ℝ) s := by
    rw [hRows]
    exact he A u z s
  have h := countedFiniteCalibrationDecision_eq P zlo zhi estimate (fun _ _ _ _ => 0)
    q hG hE k i value H hRank
  have hJ : q.selected=mixturePolicyIndex J
      (a.2.1,ProphetSecretary.Probability.uniformGridRound (2^c) (by positivity) a.2.2) d.2.2.2.2 :=
    hSelected
  have hData : rankCalibrationData ((fun i j => (data i j : ℝ)),d) =
      ((reservoirCoordinates (calibrationRowsCast y),d.1),
        fun j => ((fun i => (x j i : ℝ)),d.2.1 j)) := rfl
  change (countedFiniteCalibrationDecision P zlo zhi q i value H).1 = _
  rw [h,hJ,hRows,hTimes,hSeed]
  simp only [rankCalibratedSamplePolicy]
  have hData' : rankCalibrationData ((fun i j => (data i j : ℝ)),interpretRankCalibrationBits b c bits) =
      ((reservoirCoordinates (calibrationRowsCast y),d.1),
        fun j => ((fun i => (x j i : ℝ)),d.2.1 j)) := hData
  rw [hData']
  simp only [a,d,rankValidationPrepare,MeasurableEquiv.symm_apply_apply]

end ProphetSecretary.Statistics.Calibration
