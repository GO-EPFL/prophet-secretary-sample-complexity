import ProphetSecretary.Statistics.CalibratedOuter.BinaryExecutable
import ProphetSecretary.Statistics.CalibratedOuter.BinaryExecutablePolynomial
import ProphetSecretary.Statistics.CalibratedOuter.BinaryReward
import ProphetSecretary.Statistics.CalibratedOuter.BinaryGuarantees

/-!
# The bounded learner on rational observations

The executable rank program realizes the measured learner on the same
two sample blocks and fair bits. Casting rational observations preserves
the joint law, so both reward and each reach probability transfer.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

namespace FairCalibrationParameters

structure BinaryBoundedPrepared (n m : ℕ) where
  grid : ℕ
  schedule : FairCallSchedule
  state : BinaryBoundedRankPreparation n m grid (schedule.Seed n)
  accuracy : BinaryRational
  copies : ℕ
  copies_eq : copies=(countedConfidenceLevel schedule.failure schedule.confidence).1
  work : ℕ

noncomputable def prepareBinaryBoundedModel (a : FairCalibrationParameters n m)
    (mu z : BinaryRational) (hz : (z.value : ℝ)=a.zlo)
    (y : Fin n → Fin (2*m) → BinaryRational) (bits : a.NativeBits z.value hz) :
    BinaryBoundedPrepared n m :=
  let q := countedBinaryLearnerStartup n m a.grid z
  let H := countedBinaryLearnerStartup_value a z hz
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule z.value hz
  let p := countedBinaryBoundedRankPrepare T P q.target.halfCopies q.threshold.halfCopies
    H.2.2.2.2.1 H.2.2.2.2.2.2.2 mu z (BinaryRational.ofRat (1/4)) (q.inputs 1) (q.inputs 3)
    (fun i j => y i (finiteTrainingIndex m j)) (fun j i => y i (finiteValidationIndex m j))
    a.clockBits a.coinBits bits
  ⟨a.grid,P,p,q.inputs 3,q.threshold.halfCopies,H.2.2.2.2.2.2.2,q.work+p.work+3⟩

def BinaryPublicSetup.prepareBoundedAt {a : FairCalibrationParameters n m} {z : BinaryRational}
    {hz : (z.value : ℝ)=a.zlo} (q : a.BinaryPublicSetup z hz) (mu : BinaryRational)
    (y : Fin n → Fin (2*m) → BinaryRational) (seed : a.NativeBits z.value hz) (b c : ℕ)
    (hb : b=a.clockBits) (hc : c=a.coinBits) : BinaryBoundedPrepared n m :=
  let bits : RankCalibrationBits n m q.grid b c (q.target.Seed n) (q.threshold.Seed n) :=
    cast (by rw [q.grid_eq,q.target_eq,q.threshold_eq,hb,hc]) seed
  let p := countedBinaryBoundedRankPrepare q.target q.threshold q.startup.target.halfCopies
    q.startup.threshold.halfCopies q.targetCopies q.thresholdCopies mu z (BinaryRational.ofRat (1/4))
    (q.startup.inputs 1) (q.startup.inputs 3) (fun i j => y i (finiteTrainingIndex m j))
    (fun j i => y i (finiteValidationIndex m j)) b c bits
  ⟨q.grid,q.threshold,p,q.startup.inputs 3,q.startup.threshold.halfCopies,q.thresholdCopies,
    q.startup.work+p.work+3⟩

lemma BinaryPublicSetup.prepareBoundedAt_eq {a : FairCalibrationParameters n m} {z : BinaryRational}
    {hz : (z.value : ℝ)=a.zlo} (q : a.BinaryPublicSetup z hz) (mu : BinaryRational)
    (y : Fin n → Fin (2*m) → BinaryRational) (seed : a.NativeBits z.value hz) (b c : ℕ)
    (hb : b=a.clockBits) (hc : c=a.coinBits) :
    q.prepareBoundedAt mu y seed b c hb hc=a.prepareBinaryBoundedModel mu z hz y seed := by
  subst b c
  obtain ⟨J,T,P,s,hJ,hT,hP,hs,hct,hcp,w,hw⟩ := q
  subst J T P s
  rfl

def prepareExecutableBinaryBounded (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo)
    (y : Fin n → Fin (2*m) → BinaryRational) (seed : a.NativeBits z.value hz) :
    BinaryBoundedPrepared n m × ℕ :=
  let q := a.binaryPublicSetup z hz
  let d := countedBinaryPublicIntegers n m a.clockInverse
  let h := countedBinaryPublicIntegers_value n m a.clockInverse
  (q.prepareBoundedAt mu y seed d.clockBits d.coinBits h.1 h.2.1,q.extraWork+d.work)

lemma prepareExecutableBinaryBounded_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo)
    (y : Fin n → Fin (2*m) → BinaryRational) (seed : a.NativeBits z.value hz) :
    (a.prepareExecutableBinaryBounded mu z hz y seed).1=a.prepareBinaryBoundedModel mu z hz y seed :=
  let h := countedBinaryPublicIntegers_value n m a.clockInverse
  (a.binaryPublicSetup z hz).prepareBoundedAt_eq mu y seed _ _ h.1 h.2.1

def BinaryBoundedPrepared.decide (q : BinaryBoundedPrepared n m)
    (y : Fin n → Fin (2*m) → BinaryRational) (i : Fin n)
    (x : BinaryRational) (H : BinaryOuterHistory n (Fin n)) : Bool×ℕ :=
  countedBinaryBoundedRankDecision q.schedule q.copies q.copies_eq
    (fun i j => y i (finiteTrainingIndex m j)) q.accuracy q.state i x H

set_option maxHeartbeats 800000 in
theorem decideExecutableBinaryBounded_value (a : FairCalibrationParameters n m)
    (mu z : BinaryRational) (hz : (z.value : ℝ)=a.zlo) (y : Fin n → Fin (2*m) → BinaryRational)
    (bits : a.NativeBits z.value hz) (k i : Fin n) (x : BinaryRational)
    (H : BinaryOuterHistory n (Fin n)) (hRank : onlineQueryRank (binaryOuterHistoryValue H) i=k) :
    ((a.prepareExecutableBinaryBounded mu z hz y bits).1.decide y i x H).1 =
      (a.finiteLearner (mu.value : ℝ)).policy.decide
        ((fun i j => ((y i j).value : ℝ)),a.nativeCalibrationBitsToMeasured z.value hz bits)
        k i (x.value : ℝ) (calibrationRankHistoryCast (binaryOuterHistoryValue H)) := by
  rw [a.prepareExecutableBinaryBounded_eq]
  let q := countedBinaryLearnerStartup n m a.grid z
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule z.value hz
  have hh := countedBinaryLearnerStartup_value a z hz
  have h := countedBinaryBoundedRankDecision_value T P q.target.halfCopies q.threshold.halfCopies
    hh.2.2.2.2.1 hh.2.2.2.2.2.2.2 mu z (BinaryRational.ofRat (1/4)) (q.inputs 1) (q.inputs 3)
    hh.1 hh.2.1 (fun i j => y i (finiteTrainingIndex m j)) (fun j i => y i (finiteValidationIndex m j))
    a.clockBits a.coinBits bits i x H
  simp only [BinaryRational.ofRat_value] at h
  let Y := fun i j => (y i j).value
  let N := countedFiniteCalibrationPrepare T P a.clockBits a.coinBits mu.value z.value (1/4)
    (nativeCalibrationCutoff m) (fun i j => Y i (finiteTrainingIndex m j))
    (fun j i => Y i (finiteValidationIndex m j)) bits
  have hv := a.nativeFiniteDecision_eq_finiteLearner mu.value z.value hz Y bits k i x.value
    (binaryOuterHistoryValue H) hRank
  refine h.trans ?_
  change (countedFiniteCalibrationDecision P z.value (1/4) N i x.value H).1=_
  refine (show (countedFiniteCalibrationDecision P z.value (1/4) N i x.value H).1=
    (countedFiniteCalibrationDecision P z.value (1/4) N i x.value (binaryOuterHistoryValue H)).1 from ?_).trans hv
  let f := fun a : Fin n × BinaryRational => (a.1,a.2.value)
  have hSet : onlineContinuationSet N.rows (binaryOuterHistoryValue H) i=onlineContinuationSet N.rows H i := by
    ext j
    cases he : H j <;> simp [onlineContinuationSet,binaryOuterHistoryValue,he]
  have hRank' : onlineQueryRank (binaryOuterHistoryValue H) i=onlineQueryRank H i := onlineQueryRank_map H f i
  unfold countedFiniteCalibrationDecision countedOnlineCalibrationDecision
  rw [hSet,hRank']

noncomputable def boundedBinaryAccepted (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (bits : a.NativeBits z.value hz) (y : Fin n → Fin (2*m) → ℚ)
    (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  let data := fun i j => BinaryRational.ofRat (y i j)
  let q := (a.prepareExecutableBinaryBounded mu z hz data bits).1
  Finset.univ.filter fun i => (q.decide data i (BinaryRational.ofRat (x i))
    (encodedRankHistory p x (p.symm i))).1=true

lemma boundedBinaryAccepted_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (bits : a.NativeBits z.value hz) (y : Fin n → Fin (2*m) → ℚ)
    (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    a.boundedBinaryAccepted mu z hz bits y x p =
      (a.finiteLearner (mu.value : ℝ)).policy.accepted
        ((fun i j => (y i j : ℝ)),a.nativeCalibrationBitsToMeasured z.value hz bits) p (fun i => (x i : ℝ)) := by
  ext i
  have hr : onlineQueryRank (binaryOuterHistoryValue (encodedRankHistory p x (p.symm i))) i=p.symm i := by
    rw [encodedRankHistory_value]
    exact rationalRankHistory_currentRank p x (p.symm i) i
  have h := a.decideExecutableBinaryBounded_value mu z hz (fun i j => BinaryRational.ofRat (y i j))
    bits (p.symm i) i (BinaryRational.ofRat (x i)) (encodedRankHistory p x (p.symm i)) hr
  rw [encodedRankHistory_value,rationalRankHistory_cast] at h
  simp only [BinaryRational.ofRat_value] at h
  simp only [boundedBinaryAccepted,Finset.mem_filter,Finset.mem_univ,true_and,RankPolicy.mem_accepted,RankPolicy.action]
  rw [h]

noncomputable def boundedBinaryWorldLaw (a : FairCalibrationParameters n m) (z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (P : RationalOfferInstance n) :
    Measure ((Fin n → ℚ) × (Equiv.Perm (Fin n) × ((Fin n → Fin (2*m) → ℚ) × a.NativeBits z.value hz))) :=
  P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.samplesLaw (2*m)).prod
    (rankCalibrationBitsLaw a.clockBits a.coinBits (nativeScheduleLaw n a.nativeTargetSchedule)
      (nativeScheduleLaw n (a.nativeThresholdSchedule z.value hz)))))

noncomputable def boundedBinaryExpectedReward (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (P : RationalOfferInstance n) : ℝ :=
  ∫ w, let A := a.boundedBinaryAccepted mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1
    ∑ i : Fin n, if i∈A ∧ (∀ j∈A,w.2.1.symm i≤w.2.1.symm j) then (w.1 i : ℝ) else 0
    ∂a.boundedBinaryWorldLaw z hz P

noncomputable def boundedBinaryReachProbability (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (P : RationalOfferInstance n) (i : Fin n) : ℝ :=
  (a.boundedBinaryWorldLaw z hz P).real {w |
    ∀ j∈a.boundedBinaryAccepted mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1,w.2.1.symm i≤w.2.1.symm j}

theorem boundedBinary_expectations_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (P : RationalOfferInstance n) :
    a.boundedBinaryExpectedReward mu z hz P=(a.finiteLearner (mu.value : ℝ)).expectedReward P.toInstance ∧
    ∀ i,a.boundedBinaryReachProbability mu z hz P i=
      (a.finiteLearner (mu.value : ℝ)).reachProbability P.toInstance i := by
  let L := a.finiteLearner (mu.value : ℝ)
  let π := L.randomizedPolicy P.toInstance
  let A := (Fin n → ℚ) × (Equiv.Perm (Fin n) × ((Fin n → Fin (2*m) → ℚ) × a.NativeBits z.value hz))
  let f : A → π.World := fun w => ((fun i => (w.1 i : ℝ)),w.2.1,(fun i j => (w.2.2.1 i j : ℝ)),
    a.nativeCalibrationBitsToMeasured z.value hz w.2.2.2)
  have h : MeasurePreserving f (a.boundedBinaryWorldLaw z hz P) (π.worldLaw P.toInstance) :=
    P.cast_values_measurePreserving.prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
      ((P.cast_samples_measurePreserving _).prod
        (a.nativeCalibrationBitsToMeasured_measurePreserving z.value hz a.clockBits a.coinBits)))
  constructor
  · calc
      _ = ∫ w : A, π.realizedReward (f w) ∂a.boundedBinaryWorldLaw z hz P := by
        unfold boundedBinaryExpectedReward
        apply integral_congr_ae
        apply ae_of_all
        intro w
        dsimp only
        rw [a.boundedBinaryAccepted_eq]
        change _=L.policy.reward ((fun i j => (w.2.2.1 i j : ℝ)),
          a.nativeCalibrationBitsToMeasured z.value hz w.2.2.2) w.2.1 (fun i => (w.1 i : ℝ))
        unfold RankPolicy.reward
        apply Finset.sum_congr rfl
        intro i _
        let Y : Reservoir n (2*m) := fun i j => (w.2.2.1 i j : ℝ)
        let r : L.Seed := a.nativeCalibrationBitsToMeasured z.value hz w.2.2.2
        let X := fun i => (w.1 i : ℝ)
        let S := L.policy.accepted (Y,r) w.2.1 X
        have hI : L.policy.Selects (Y,r) w.2.1 X i ↔
            i∈S ∧ ∀ j∈S,w.2.1.symm i≤w.2.1.symm j := Iff.rfl
        change (if i∈S ∧ (∀ j∈S,w.2.1.symm i≤w.2.1.symm j) then X i else 0)=
          (if L.policy.Selects (Y,r) w.2.1 X i then X i else 0)
        by_cases hi : L.policy.Selects (Y,r) w.2.1 X i
        · rw [if_pos (hI.mp hi),if_pos hi]
        · rw [if_neg (mt hI.mpr hi),if_neg hi]
      _ = _ := h.hasLaw.integral_comp π.measurable_realizedReward.aestronglyMeasurable
  · intro i
    let E := {ω : π.World | L.policy.Reaches ω.2.2 ω.2.1 ω.1 i}
    have hE : MeasurableSet E := L.policy.measurableSet_reaches L.policy_isMeasurable
      (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst) i
    have hPre : {w : A | ∀ j∈a.boundedBinaryAccepted mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1,
        w.2.1.symm i≤w.2.1.symm j}=f ⁻¹' E := by
      ext w
      change (∀ j∈a.boundedBinaryAccepted mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1,
        w.2.1.symm i≤w.2.1.symm j) ↔ L.policy.Reaches ((fun i j => (w.2.2.1 i j : ℝ)),
          a.nativeCalibrationBitsToMeasured z.value hz w.2.2.2) w.2.1 (fun i => (w.1 i : ℝ)) i
      rw [RankPolicy.Reaches,a.boundedBinaryAccepted_eq]
    unfold boundedBinaryReachProbability RankLearner.reachProbability
    rw [hPre,Measure.real,h.measure_preimage hE.nullMeasurableSet]
    rfl

end FairCalibrationParameters

/-- The mean floor can be fixed rationally before any samples arrive.
The binary program preserves both guarantees of the measured learner. -/
theorem exists_binary_bounded_rank_learner (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ mu' : ℚ, mu/2≤(mu' : ℝ) ∧ (mu' : ℝ)≤mu ∧
      ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
        (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (K : ℝ), 0<K ∧
        ∀ (n m : ℕ) (hn : 0<n) (hm : 2≤m) (P : RationalOfferInstance n),
          (∀ i, ∀ᵐ x ∂P.toInstance.law i,x≤1) →
          mu≤P.toInstance.expectedMaximum → P.toInstance.expectedMaximum≤1/80 →
          P.toInstance.positiveCount≤2*Real.log (m : ℝ) →
          let a : FairCalibrationParameters n m :=
            ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
          let z := BinaryRational.ofRat ((1-b)/b)
          let hz : (z.value : ℝ)=a.zlo := by
            simp only [z,BinaryRational.ofRat_value,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
            rfl
          let r := BinaryRational.ofRat mu'
          optimalCompetitiveRatio*P.toInstance.expectedMaximum-K/(m : ℝ)≤a.boundedBinaryExpectedReward r z hz P ∧
          ∀ i,optimalCompetitiveRatio-K/(m : ℝ)≤a.boundedBinaryReachProbability r z hz P i := by
  obtain ⟨r,hLo,hHi,b,hb,zInv,hInv,K,hK,hB⟩ := exists_rational_finite_rank_calibrated_learner mu hmu hmuHi
  refine ⟨r,hLo,hHi,b,hb,zInv,hInv,K,hK,?_⟩
  intro n m hn hm P hcap hM hSmall hL
  dsimp only
  have hh := hB n m hn hm P.toInstance hcap hM hSmall hL
  dsimp only at hh
  let a : FairCalibrationParameters n m :=
    ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
  let z := BinaryRational.ofRat ((1-b)/b)
  have hz : (z.value : ℝ)=a.zlo := by
    simp only [z,BinaryRational.ofRat_value,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
    rfl
  have hE := a.boundedBinary_expectations_eq (BinaryRational.ofRat r) z hz P
  refine ⟨?_,?_⟩
  · change _≤a.boundedBinaryExpectedReward (BinaryRational.ofRat r) z hz P
    rw [hE.1,BinaryRational.ofRat_value]
    exact hh.1
  · intro i
    change _≤a.boundedBinaryReachProbability (BinaryRational.ofRat r) z hz P i
    rw [hE.2 i,BinaryRational.ofRat_value]
    exact hh.2 i

namespace BinaryScheduleInput

variable {zlo : ℚ} {zInv : ℕ}

noncomputable def executableBoundedWorkBudget (x : BinaryScheduleInput zlo zInv) (D : ℕ) : ℕ :=
  x.boundedPrepareBudgetAt x.width D+x.n*x.boundedOnlineBudgetAt x.width D+
    x.publicStartupBudget D+x.executableSetupBudget D+1

theorem executableBoundedWorkBudget_polynomial (D : ℕ) :
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv)) (fun x => x.executableBoundedWorkBudget D) := by
  let N := size (zlo := zlo) (zInv := zInv)
  have hN : ∀ x,0<N x := by intro x; unfold N size; omega
  have hY : HasPolynomialWorkBound N (fun x => x.width) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hn : HasPolynomialWorkBound N (fun x => x.n) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  obtain ⟨hp,ho,hs⟩ := boundedWorkBudgets_polynomial D _ hY
  exact (((hp.add hN (hn.mul ho)).add hN hs).add hN (executableSetupBudget_polynomial D)).add hN
    (HasPolynomialWorkBound.const N 1)

set_option maxHeartbeats 800000 in
/-- Count the complete preparation and the decisions at any subset of
arrivals. The input width applies to every represented observation. -/
theorem executableBoundedProgram_work (x : BinaryScheduleInput zlo zInv) (D : ℕ)
    (mu z : BinaryRational) (ez : z.value=zlo) (hD : 2≤D)
    (hmu : RationalHeight mu.value D) (hz : RationalHeight z.value D)
    (data : Fin x.n → Fin (2*x.m) → BinaryRational)
    (hy : ∀ i j,RationalHeight (data i j).value x.width)
    (bits : x.parameters.NativeBits z.value (by rw [ez]; exact x.coefficient_eq))
    (S : Finset (Fin x.n)) (offer : Fin x.n → BinaryRational)
    (hist : Fin x.n → BinaryOuterHistory x.n (Fin x.n))
    (ho : ∀ i,RationalHeight (offer i).value x.width) :
    let Q := x.parameters.prepareExecutableBinaryBounded mu z (by rw [ez]; exact x.coefficient_eq) data bits
    Q.1.work+Q.2+(∑ i∈S,(Q.1.decide data i (offer i) (hist i)).2)≤x.executableBoundedWorkBudget D := by
  subst zlo
  let a := x.parameters
  let hZ : (z.value : ℝ)=a.zlo := x.coefficient_eq
  let Q := a.prepareExecutableBinaryBounded mu z hZ data bits
  let A := binaryLearnerAccuracyWidth x.n x.m a.grid D
  let st := countedBinaryLearnerStartup x.n x.m a.grid z
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule z.value hZ
  let Y := fun i j => data i (finiteTrainingIndex x.m j)
  let X := fun j i => data i (finiteValidationIndex x.m j)
  let U := BinaryRational.ofRat (1/4)
  have e := countedBinaryLearnerStartup_value a z hZ
  have hs := countedBinaryLearnerStartup_bounds x.n x.m a.grid D z hz
  have hM : x.m≤2^x.m := (Nat.lt_two_pow_self (n := x.m)).le
  have hJ : a.grid≤2^x.m := (familyGridSize_le (by linarith only [a.coefficient_mem.1])).trans hM
  have hU : RationalHeight U.value D := by
    rw [BinaryRational.ofRat_value]
    have hh : RationalHeight (1/4:ℚ) 2 := by
      simpa only [Int.cast_one,Int.cast_ofNat] using
        rationalHeight_of_fraction 1 4 (by decide) 2 (by decide) (by decide)
    exact hh.mono hD
  have hp := countedBinaryBoundedRankPrepare_work T P st.target.halfCopies st.threshold.halfCopies
    e.2.2.2.2.1 e.2.2.2.2.2.2.2 mu z U (st.inputs 1) (st.inputs 3) Y X a.clockBits a.coinBits bits
    x.width x.m D x.m A A (fun i j => hy i _) (fun j i => hy i _) hM hJ hmu hz hU (hs.1 1) (hs.1 3)
  have hPrep : Q.1.work≤x.boundedPrepareBudgetAt x.width D+x.publicStartupBudget D+1 := by
    change (a.prepareExecutableBinaryBounded mu z hZ data bits).1.work≤_
    rw [a.prepareExecutableBinaryBounded_eq]
    change st.work+(countedBinaryBoundedRankPrepare T P st.target.halfCopies st.threshold.halfCopies
      e.2.2.2.2.1 e.2.2.2.2.2.2.2 mu z U (st.inputs 1) (st.inputs 3) Y X a.clockBits a.coinBits bits).work+3≤_
    let G := binaryBoundedRankPrepareWork T P x.n x.m a.grid a.clockBits a.coinBits x.width x.m D x.m A A
    change _≤G+2+x.publicStartupBudget D+1
    change _≤G at hp
    have hS' : st.work≤x.publicStartupBudget D := hs.2
    omega
  have hExtra : Q.2≤x.executableSetupBudget D := by
    have h := a.binaryPublicSetup_extra_work z hZ D hz
    have hI := countedBinaryPublicIntegers_work x.n x.m a.clockInverse
    change (a.binaryPublicSetup z hZ).extraWork+(countedBinaryPublicIntegers x.n x.m a.clockInverse).work≤_
    unfold executableSetupBudget
    exact Nat.add_le_add h (hI.trans_eq (congrArg (binaryPublicIntegersWork x.n x.m) x.inverse_eq))
  have hOn (i : Fin x.n) : (Q.1.decide data i (offer i) (hist i)).2≤x.boundedOnlineBudgetAt x.width D := by
    change ((a.prepareExecutableBinaryBounded mu z hZ data bits).1.decide data i (offer i) (hist i)).2≤_
    rw [a.prepareExecutableBinaryBounded_eq]
    exact countedBinaryBoundedRankDecision_work T P st.target.halfCopies st.threshold.halfCopies
      e.2.2.2.2.1 e.2.2.2.2.2.2.2 mu z U (st.inputs 1) (st.inputs 3) Y X a.clockBits a.coinBits bits
      i (offer i) (hist i) x.width x.m D x.m A (fun i j => hy i _) (ho i) hM hJ hz hU (hs.1 3)
  have hSum : (∑ i∈S,(Q.1.decide data i (offer i) (hist i)).2)≤x.n*x.boundedOnlineBudgetAt x.width D := by
    calc
      _ ≤ ∑ _i∈S,x.boundedOnlineBudgetAt x.width D := Finset.sum_le_sum (fun i _ => hOn i)
      _ = S.card*x.boundedOnlineBudgetAt x.width D := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_univ S |>.trans_eq (Fintype.card_fin _))
  change Q.1.work+Q.2+(∑ i∈S,(Q.1.decide data i (offer i) (hist i)).2)≤_
  unfold executableBoundedWorkBudget
  omega

theorem boundedRankBitAllocation (x : BinaryScheduleInput zlo zInv)
    (drawBit : StateM ℕ Bool) (hBit : ∀ c,(drawBit.run c).2=c+1) (d : ℕ) :
    let a := x.parameters
    let T := a.nativeTargetSchedule
    let P := a.nativeThresholdSchedule zlo x.coefficient_eq
    let q := (sampleRankCalibrationBitsM x.n x.m a.grid
      T.bits (confidenceCopyCount T.failure T.confidence) T.level
      P.bits (confidenceCopyCount P.failure P.confidence) P.level a.clockBits a.coinBits drawBit).run d
    q.2-d≤x.bitBudget ∧ q.1.2≤x.allocationBudget+
      rankAuxiliaryBitStorageWork x.n x.m a.clockBits a.coinBits+2 := by
  let a := x.parameters
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo x.coefficient_eq
  let CT := confidenceCopyCount T.failure T.confidence
  let CP := confidenceCopyCount P.failure P.confidence
  let q := (sampleRankCalibrationBitsM x.n x.m a.grid T.bits CT T.level P.bits CP P.level
    a.clockBits a.coinBits drawBit).run d
  change q.2-d≤x.bitBudget ∧ q.1.2≤x.allocationBudget+
    rankAuxiliaryBitStorageWork x.n x.m a.clockBits a.coinBits+2
  constructor
  · have hq : q.2=d+(4*x.m+1)*fairQueryBankBitCount x.n T.bits CT T.level+
        (x.m+1)*x.n*(a.grid+1)*fairQueryBankBitCount x.n P.bits CP P.level+
        (2*x.m+1)*x.n*a.clockBits+a.coinBits :=
      sampleRankCalibrationBitsM_counter x.n x.m a.grid T.bits CT T.level P.bits CP P.level
        a.clockBits a.coinBits drawBit hBit d
    rw [hq]
    have hT := Nat.mul_le_mul_left (4*x.m+1) (fairQueryBankBitCount_le x.n T.bits CT T.level)
    have hP := Nat.mul_le_mul_left ((x.m+1)*x.n*(a.grid+1)) (fairQueryBankBitCount_le x.n P.bits CP P.level)
    unfold bitBudget finiteScheduleFairBitsBound
    rw [show (2*x.m+1)*x.n*a.clockBits=x.n*(2*x.m+1)*a.clockBits by ring]
    dsimp only [a,T,P,CT,CP] at hT hP ⊢
    omega
  · have hq : q.1.2≤finiteQueryStorageBound x.n x.m a.grid T P+
        rankAuxiliaryBitStorageWork x.n x.m a.clockBits a.coinBits+2 :=
      sampleRankCalibrationBitsM_work x.n x.m a.grid T.bits CT T.level P.bits CP P.level
        a.clockBits a.coinBits drawBit d
    have hA : finiteQueryStorageBound x.n x.m a.grid T P≤x.allocationBudget := by
      unfold allocationBudget finiteScheduleArithmeticBound
      change finiteQueryStorageBound x.n x.m a.grid T P≤finiteQueryStorageBound x.n x.m a.grid T P+_+_
      omega
    omega

end BinaryScheduleInput

/-- The request loop reads both blocks for each distribution. -/
theorem boundedRankTraining_marginalCount {A : Type} (n m : ℕ) (j : Fin n)
    (sample : Fin n → StateM ℕ A)
    (h : ∀ i c, ((sample i).run c).2=c+(if i=j then 1 else 0)) (s : ℕ) :
    ((countedFullSamplesM n (2*m) sample).run s).2=s+2*m :=
  countedFullSamplesM_marginalCounter n (2*m) j sample h s

end ProphetSecretary.Statistics.Calibration
