import ProphetSecretary.Statistics.NativeFairSchedules

/-!
# Native calls for the public fair-calibration parameters

The target and threshold schedules below use rational tolerances and
failure probabilities. Their banks reindex to the exact measured target
and continuation calls, with the same public depth and precision.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis ProphetSecretary.Probability

namespace FairCalibrationParameters

variable {n m : ℕ}

def rationalTargetTolerance (m : ℕ) : ℚ := 1/(m : ℚ)

def rationalTargetFailure (m : ℕ) : ℚ :=
  1/((m : ℚ)^2*(4*(m : ℚ)+1))

def rationalThresholdTolerance (m : ℕ) (zlo : ℚ) : ℚ :=
  zlo/((m : ℚ)*(1+(4*(Nat.clog 2 m : ℚ)+2))^2)/2

def rationalThresholdFailure (n m J : ℕ) : ℚ :=
  1/((m : ℚ)^2*(n : ℚ)*((J : ℚ)+1))

lemma rationalGrid_eq (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :
    rationalFamilyGridSize m zlo (1/4)=a.grid := by
  rw [rationalFamilyGridSize_eq,hz]
  norm_num [FairCalibrationParameters.grid]

lemma rationalTargetTolerance_cast (a : FairCalibrationParameters n m) :
    (rationalTargetTolerance m : ℝ)=a.targetTolerance := by
  simp only [rationalTargetTolerance,FairCalibrationParameters.targetTolerance,
    Rat.cast_div,Rat.cast_one,Rat.cast_natCast]

lemma rationalTargetFailure_cast (a : FairCalibrationParameters n m) :
    (rationalTargetFailure m : ℝ)=a.targetFailure := by
  simp only [rationalTargetFailure,FairCalibrationParameters.targetFailure,
    Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add]

lemma rationalThresholdTolerance_cast (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) :
    (rationalThresholdTolerance m zlo : ℝ)=a.thresholdTolerance := by
  simp only [rationalThresholdTolerance,FairCalibrationParameters.thresholdTolerance,policyAccuracy,
    targetCountCutoff,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_natCast,Rat.cast_add,hz]

lemma rationalThresholdFailure_cast (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) :
    (rationalThresholdFailure n m (rationalFamilyGridSize m zlo (1/4)) : ℝ)=a.thresholdFailure := by
  simp only [rationalThresholdFailure,FairCalibrationParameters.thresholdFailure,policyFailureBound,
    Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_add,
    rationalGrid_eq a zlo hz]

private lemma sampleCount_nonzero (a : FairCalibrationParameters n m) : NeZero m :=
  ⟨by have := a.two_le; omega⟩

def nativeTargetSchedule (a : FairCalibrationParameters n m) : FairCallSchedule :=
  letI := sampleCount_nonzero a
  nativePublicFairSchedule n m (rationalTargetTolerance m) (rationalTargetFailure m)
    (a.rationalTargetTolerance_cast.symm ▸ a.targetTolerance_mem)
    (a.rationalTargetFailure_cast.symm ▸ a.targetFailure_range)

def nativeThresholdSchedule (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) : FairCallSchedule :=
  letI := sampleCount_nonzero a
  nativePublicFairSchedule n m (rationalThresholdTolerance m zlo)
    (rationalThresholdFailure n m (rationalFamilyGridSize m zlo (1/4)))
    ((a.rationalThresholdTolerance_cast zlo hz).symm ▸ a.thresholdTolerance_mem)
    ((a.rationalThresholdFailure_cast zlo hz).symm ▸ a.thresholdFailure_range)

private lemma calibrationFairPrecision_congr (n m : ℕ) [NeZero m] {h h' : ℝ} (e : h=h')
    (hh : h∈Ioo (0 : ℝ) 1) (hh' : h'∈Ioo (0 : ℝ) 1) :
    calibrationFairPrecision n m h hh=calibrationFairPrecision n m h' hh' := by
  subst h'
  rfl

lemma nativeTargetSchedule_bits (a : FairCalibrationParameters n m) :
    a.nativeTargetSchedule.bits=a.targetBits := by
  letI := sampleCount_nonzero a
  unfold nativeTargetSchedule FairCalibrationParameters.targetBits
  rw [nativePublicFairSchedule_bits]
  exact calibrationFairPrecision_congr n m a.rationalTargetTolerance_cast _ _

lemma nativeThresholdSchedule_bits (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) :
    (a.nativeThresholdSchedule zlo hz).bits=a.thresholdBits := by
  letI := sampleCount_nonzero a
  unfold nativeThresholdSchedule FairCalibrationParameters.thresholdBits
  rw [nativePublicFairSchedule_bits]
  exact calibrationFairPrecision_congr n m (a.rationalThresholdTolerance_cast zlo hz) _ _

lemma nativeTargetSchedule_level (a : FairCalibrationParameters n m) :
    a.nativeTargetSchedule.level=calibrationPlannerLevel m (a.targetTolerance/2) := by
  letI := sampleCount_nonzero a
  unfold nativeTargetSchedule
  rw [nativePublicFairSchedule_level,a.rationalTargetTolerance_cast]

lemma nativeThresholdSchedule_level (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) :
    (a.nativeThresholdSchedule zlo hz).level=calibrationPlannerLevel m (a.thresholdTolerance/2) := by
  letI := sampleCount_nonzero a
  unfold nativeThresholdSchedule
  rw [nativePublicFairSchedule_level,a.rationalThresholdTolerance_cast zlo hz]

noncomputable def nativeTargetSeed (a : FairCalibrationParameters n m) :
    a.nativeTargetSchedule.Seed n → a.TargetSeed :=
  scheduledFairSeed a.nativeTargetSchedule n m a.targetBits a.targetTolerance a.targetFailure
    a.targetFailure_range a.nativeTargetSchedule_bits a.rationalTargetFailure_cast a.nativeTargetSchedule_level

noncomputable def nativeThresholdSeed (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :
    (a.nativeThresholdSchedule zlo hz).Seed n → a.ThresholdSeed :=
  scheduledFairSeed (a.nativeThresholdSchedule zlo hz) n m a.thresholdBits a.thresholdTolerance a.thresholdFailure
    a.thresholdFailure_range (a.nativeThresholdSchedule_bits zlo hz)
    (a.rationalThresholdFailure_cast zlo hz) (a.nativeThresholdSchedule_level zlo hz)

instance fairCallScheduleSeedMeasurableSpace (n : ℕ) (S : FairCallSchedule) :
    MeasurableSpace (S.Seed n) := by
  unfold FairCallSchedule.Seed FairQueryBank MultilevelSeedBank
  infer_instance

instance fairCalibrationTargetSeedMeasurableSpace (a : FairCalibrationParameters n m) :
    MeasurableSpace a.TargetSeed := by
  unfold FairCalibrationParameters.TargetSeed CalibrationFairSeed
  infer_instance

instance fairCalibrationThresholdSeedMeasurableSpace (a : FairCalibrationParameters n m) :
    MeasurableSpace a.ThresholdSeed := by
  unfold FairCalibrationParameters.ThresholdSeed CalibrationFairSeed
  infer_instance

noncomputable def nativeScheduleLaw (n : ℕ) (S : FairCallSchedule) : Measure (S.Seed n) :=
  fairQueryBankLaw n S.bits (confidenceCopyCount S.failure S.confidence) S.level

private lemma probability_of_measurePreserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} [IsProbabilityMeasure μ] {ν : Measure B} {f : A → B}
    (h : MeasurePreserving f μ ν) : IsProbabilityMeasure ν := by
  refine ⟨?_⟩
  simpa only [preimage_univ,measure_univ] using
    (h.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet).symm

private lemma sigmaFinite_of_probability {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : IsProbabilityMeasure μ) : SigmaFinite μ := by
  letI : IsFiniteMeasure μ := ⟨by rw [h.measure_univ]; exact ENNReal.one_lt_top⟩
  exact IsFiniteMeasure.toSigmaFinite μ

instance nativeScheduleLaw_probability (n : ℕ) (S : FairCallSchedule) :
    IsProbabilityMeasure (nativeScheduleLaw n S) := by
  let C := confidenceCopyCount S.failure S.confidence
  have h := measurePreserving_plannerFairBankFromBitTape n S.bits C S.level
  haveI : IsProbabilityMeasure (plannerQueryBitTapeLaw n S.bits C S.level) := by
    unfold plannerQueryBitTapeLaw
    infer_instance
  exact probability_of_measurePreserving h

lemma nativeTargetSeed_measurePreserving (a : FairCalibrationParameters n m) :
    MeasurePreserving a.nativeTargetSeed (nativeScheduleLaw n a.nativeTargetSchedule) a.targetLaw :=
  scheduledFairSeed_measurePreserving a.nativeTargetSchedule n m a.targetBits a.targetTolerance a.targetFailure
    a.targetFailure_range a.nativeTargetSchedule_bits a.rationalTargetFailure_cast a.nativeTargetSchedule_level

lemma nativeThresholdSeed_measurePreserving (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :
    MeasurePreserving (a.nativeThresholdSeed zlo hz) (nativeScheduleLaw n (a.nativeThresholdSchedule zlo hz)) a.thresholdLaw :=
  scheduledFairSeed_measurePreserving (a.nativeThresholdSchedule zlo hz) n m a.thresholdBits a.thresholdTolerance
    a.thresholdFailure a.thresholdFailure_range (a.nativeThresholdSchedule_bits zlo hz)
    (a.rationalThresholdFailure_cast zlo hz) (a.nativeThresholdSchedule_level zlo hz)

theorem nativeTargetCall_value (a : FairCalibrationParameters n m) (y : Fin n → Fin m → ℚ)
    (z : ℚ) (s : a.nativeTargetSchedule.Seed n) :
    ((countedFiniteTargetCall a.nativeTargetSchedule y z s).1 : ℝ)=
      a.target (calibrationRowsCast y) (z : ℝ) (a.nativeTargetSeed s) := by
  let x : ScalarPlannerListState n ℚ := (List.finRange n,1,z)
  have hv := scheduledFairBankCall_value a.nativeTargetSchedule a.targetBits a.targetTolerance a.targetFailure
    a.targetTolerance_mem a.targetFailure_range a.nativeTargetSchedule_bits a.rationalTargetTolerance_cast
    a.rationalTargetFailure_cast a.nativeTargetSchedule_level y x (List.nodup_finRange n) s
  have hA : x.1.toFinset=Finset.univ := by ext i; simp [x]
  rw [hA] at hv
  simpa only [countedFiniteTargetCall,x,Rat.cast_one,FairCalibrationParameters.target,calibrationFairTarget,
    FairCalibrationParameters.nativeTargetSeed] using hv

theorem nativeThresholdCall_value (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo)
    (y : Fin n → Fin m → ℚ) (A : Finset (Fin n)) (u z : ℚ)
    (s : (a.nativeThresholdSchedule zlo hz).Seed n) :
    ((countedFiniteThresholdCall (a.nativeThresholdSchedule zlo hz) y A u z s).1 : ℝ)=
      a.threshold (calibrationRowsCast y) A (u : ℝ) (z : ℝ) (a.nativeThresholdSeed zlo hz s) := by
  let l := countedPredicateFilter (fun i => i∈A) (List.finRange n)
  let x : ScalarPlannerListState n ℚ := (l.1,u,z)
  have hN : x.1.Nodup := by
    change l.1.Nodup
    unfold l
    rw [countedPredicateFilter_value]
    exact (List.nodup_finRange n).filter _
  have hA : x.1.toFinset=A := by
    change l.1.toFinset=A
    unfold l
    rw [countedPredicateFilter_value]
    ext i
    simp
  have hv := scheduledFairBankCall_value (a.nativeThresholdSchedule zlo hz) a.thresholdBits
    a.thresholdTolerance a.thresholdFailure a.thresholdTolerance_mem a.thresholdFailure_range
    (a.nativeThresholdSchedule_bits zlo hz) (a.rationalThresholdTolerance_cast zlo hz)
    (a.rationalThresholdFailure_cast zlo hz) (a.nativeThresholdSchedule_level zlo hz) y x hN s
  rw [hA] at hv
  simpa only [countedFiniteThresholdCall,l,x,FairCalibrationParameters.threshold,
    FairCalibrationParameters.nativeThresholdSeed] using hv

/-- Reindex the independent fair banks without changing any key, clock or coin bit. -/
noncomputable def nativeCalibrationBitsToMeasured (a : FairCalibrationParameters n m)
    (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) {b c : ℕ}
    (s : RankCalibrationBits n m a.grid b c (a.nativeTargetSchedule.Seed n)
      ((a.nativeThresholdSchedule zlo hz).Seed n)) :
    RankCalibrationBits n m a.grid b c a.TargetSeed a.ThresholdSeed :=
  (fun j => a.nativeTargetSeed (s.1 j),
    fun j => ((s.2.1 j).1,(s.2.1 j).2.1,
      fun k => a.nativeThresholdSeed zlo hz ((s.2.1 j).2.2 k)),
    s.2.2.1,(fun k => a.nativeThresholdSeed zlo hz (s.2.2.2.1 k)),s.2.2.2.2)

lemma nativeCalibrationBitsToMeasured_measurePreserving (a : FairCalibrationParameters n m)
    (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) (b c : ℕ) :
    MeasurePreserving (a.nativeCalibrationBitsToMeasured zlo hz (b := b) (c := c))
      (rankCalibrationBitsLaw b c (nativeScheduleLaw n a.nativeTargetSchedule)
        (nativeScheduleLaw n (a.nativeThresholdSchedule zlo hz)))
      (rankCalibrationBitsLaw b c a.targetLaw a.thresholdLaw) := by
  let t := nativeScheduleLaw n a.nativeTargetSchedule
  let s := nativeScheduleLaw n (a.nativeThresholdSchedule zlo hz)
  let B := rankCalibrationClockBitsLaw n b
  let C := fairBitVectorLaw c
  let J := a.grid
  have ht : IsProbabilityMeasure a.targetLaw :=
    probability_of_measurePreserving a.nativeTargetSeed_measurePreserving
  have hp : IsProbabilityMeasure a.thresholdLaw :=
    probability_of_measurePreserving (a.nativeThresholdSeed_measurePreserving zlo hz)
  letI : IsProbabilityMeasure a.targetLaw := ht
  letI : IsProbabilityMeasure a.thresholdLaw := hp
  have hT := measurePreserving_pi (fun _ : TargetGrid m => t) (fun _ : TargetGrid m => a.targetLaw)
    (hν := fun _ => sigmaFinite_of_probability a.targetLaw ht) (fun _ => a.nativeTargetSeed_measurePreserving)
  have hP := measurePreserving_pi (fun _ : Fin n × Fin (J+1) => s)
    (fun _ : Fin n × Fin (J+1) => a.thresholdLaw) (hν := fun _ => sigmaFinite_of_probability a.thresholdLaw hp)
    (fun _ => a.nativeThresholdSeed_measurePreserving zlo hz)
  have hVp : IsProbabilityMeasure (rankCalibrationValidationBitsLaw (n := n) (J := J) b a.thresholdLaw) :=
    rankCalibrationValidationBitsLaw_probability b a.thresholdLaw
  have hV := measurePreserving_pi
    (fun _ : Fin m => rankCalibrationValidationBitsLaw (n := n) (J := J) b s)
    (fun _ : Fin m => rankCalibrationValidationBitsLaw (n := n) (J := J) b a.thresholdLaw)
    (hν := fun _ => sigmaFinite_of_probability _ hVp) (fun _ => (MeasurePreserving.id B).prod ((MeasurePreserving.id B).prod hP))
  exact hT.prod (hV.prod ((MeasurePreserving.id B).prod (hP.prod (MeasurePreserving.id C))))

end FairCalibrationParameters

end ProphetSecretary.Statistics.Calibration
