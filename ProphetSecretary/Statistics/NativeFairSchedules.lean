import ProphetSecretary.Statistics.FairCalibratedLearner
import ProphetSecretary.Statistics.FiniteBitWork
import ProphetSecretary.Statistics.RationalCalibrationGrid
import ProphetSecretary.Statistics.RationalCalibrationLoops

/-!
# The native rational fair-call schedule

The rational public searches compute the same precision, level and copy
counts as the measured fair-call parameters. Reindexing the finite bank
keeps every individual bit and its independent law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ}

def rationalCalibrationWeightBound (m : ℕ) : ℚ := (4 : ℚ)^8*(2*(m : ℚ))^32

lemma rationalCalibrationWeightBound_cast (m : ℕ) :
    (rationalCalibrationWeightBound m : ℝ)=calibrationWeightBound m := by
  simp only [rationalCalibrationWeightBound,calibrationWeightBound,
    Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]

private lemma gridTolerance_ratCast (n : ℕ) (β h : ℚ) :
    ((plannerGridTolerance n β h : ℚ) : ℝ)=plannerGridTolerance n (β : ℝ) (h : ℝ) := by
  simp only [plannerGridTolerance,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_add]

private lemma nativeBitPrecision_exists (n m : ℕ) [NeZero m] (h : ℚ)
    (hh : (h : ℝ)∈Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, (1/4 : ℚ)^j≤plannerGridTolerance n (rationalCalibrationWeightBound m) h := by
  apply (exists_quarter_pow_le_ratCast _).mp
  rw [gridTolerance_ratCast,rationalCalibrationWeightBound_cast]
  exact exists_confidence_level
    (plannerGridTolerance_pos n (zero_lt_one.trans_le (calibrationWeightBound_ge_one (m := m))) hh.1)
    (plannerGridTolerance_lt_one n (calibrationWeightBound_ge_one (m := m)) hh.2.le)

private lemma nativePublicLevel_exists (m : ℕ) [NeZero m] (h : ℚ) (hh : (h : ℝ)∈Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, (1/4 : ℚ)^j≤scalarPlannerPrecisionRatio (rationalCalibrationWeightBound m) (h/2) := by
  apply (exists_quarter_pow_le_ratCast _).mp
  rw [← scalarPlannerPrecisionRatio_ratCast,rationalCalibrationWeightBound_cast]
  simp only [Rat.cast_div,Rat.cast_ofNat]
  exact scalarPlannerPrecision_exists (calibrationWeightBound_ge_one (m := m))
    ⟨by linarith [hh.1],by linarith [hh.2]⟩

private lemma nativeConfidence_exists (p : ℚ) (hp : (p : ℝ)∈Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, (1/4 : ℚ)^j≤p :=
  (exists_quarter_pow_le_ratCast p).mp (exists_confidence_level hp.1 hp.2)

def nativePublicFairSchedule (n m : ℕ) [NeZero m] (h p : ℚ)
    (hh : (h : ℝ)∈Ioo (0 : ℝ) 1) (hp : (p : ℝ)∈Ioo (0 : ℝ) 1) : FairCallSchedule :=
  ⟨(countedPlannerBitPrecision n (rationalCalibrationWeightBound m) h
    (nativeBitPrecision_exists n m h hh)).1,
   (countedScalarPlannerLevel (rationalCalibrationWeightBound m) (h/2)
    (nativePublicLevel_exists m h hh)).1,
   h,p,nativeConfidence_exists p hp⟩

lemma nativePublicFairSchedule_bits (n m : ℕ) [NeZero m] (h p : ℚ)
    (hh : (h : ℝ)∈Ioo (0 : ℝ) 1) (hp : (p : ℝ)∈Ioo (0 : ℝ) 1) :
    (nativePublicFairSchedule n m h p hh hp).bits=calibrationFairPrecision n m (h : ℝ) hh := by
  let δ := plannerGridTolerance n (rationalCalibrationWeightBound m) h
  have hδ : (δ : ℝ)=plannerGridTolerance n (calibrationWeightBound m) (h : ℝ) := by
    unfold δ
    rw [gridTolerance_ratCast,rationalCalibrationWeightBound_cast]
  let Hr := (exists_quarter_pow_le_ratCast δ).mpr (nativeBitPrecision_exists n m h hh)
  have e := congrArg Prod.fst (countedConfidenceLevel_ratCast δ (nativeBitPrecision_exists n m h hh) Hr)
  have er (u : ℝ) (Hu : ∃ j : ℕ, (1/4 : ℝ)^j≤u) (hu : u=(δ : ℝ)) :
      (countedConfidenceLevel u Hu).1=(countedConfidenceLevel δ (nativeBitPrecision_exists n m h hh)).1 := by
    subst u
    exact e
  unfold nativePublicFairSchedule calibrationFairPrecision countedPlannerBitPrecision
  dsimp only
  rw [er _ _ hδ.symm]

lemma nativePublicFairSchedule_level (n m : ℕ) [NeZero m] (h p : ℚ)
    (hh : (h : ℝ)∈Ioo (0 : ℝ) 1) (hp : (p : ℝ)∈Ioo (0 : ℝ) 1) :
    (nativePublicFairSchedule n m h p hh hp).level=calibrationPlannerLevel m ((h : ℝ)/2) := by
  let Hq := nativePublicLevel_exists m h hh
  have h₁ : (h : ℝ)/2∈Ioo (0 : ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  let H := scalarPlannerPrecision_exists (calibrationWeightBound_ge_one (m := m)) h₁
  have Hr : ∃ j : ℕ, (1/4 : ℝ)^j≤scalarPlannerPrecisionRatio
      (rationalCalibrationWeightBound m : ℝ) ((h/2 : ℚ) : ℝ) := by
    simpa only [rationalCalibrationWeightBound_cast,Rat.cast_div,Rat.cast_ofNat] using H
  have hL := countedScalarPlannerLevel_ratCast (rationalCalibrationWeightBound m) (h/2) Hq Hr
  unfold nativePublicFairSchedule calibrationPlannerLevel scalarPlannerLevel
  dsimp only
  rw [dif_pos H]
  simpa only [rationalCalibrationWeightBound_cast,Rat.cast_div,Rat.cast_ofNat] using hL.symm

def transportFairQueryBank {n b C R b' C' R' : ℕ}
    (hb : b=b') (hc : C=C') (hr : R=R') :
    FairQueryBank n b C R → FairQueryBank n b' C' R' := by
  subst b'
  subst C'
  subst R'
  exact id

lemma transportFairQueryBank_copies {n b C R C' : ℕ} (hc : C=C') (s : FairQueryBank n b C R) :
    transportFairQueryBank rfl hc rfl s=fun j i => s j (Fin.cast hc.symm i) := by
  subst C'
  rfl

lemma transportFairQueryBank_measurePreserving {n b C R b' C' R' : ℕ}
    (hb : b=b') (hc : C=C') (hr : R=R') :
    MeasurePreserving (transportFairQueryBank (n := n) hb hc hr)
      (fairQueryBankLaw n b C R) (fairQueryBankLaw n b' C' R') := by
  subst b'
  subst C'
  subst R'
  exact MeasurePreserving.id _

private lemma scheduledCopyCount_eq (S : FairCallSchedule) {p : ℝ}
    (hp : p∈Ioo (0 : ℝ) 1) (hP : (S.failure : ℝ)=p) :
    confidenceCopyCount S.failure S.confidence =
      confidenceCopyCount p (exists_confidence_level hp.1 hp.2) := by
  subst p
  exact (confidenceCopyCount_ratCast _ _ _).symm

noncomputable def scheduledFairSeed (S : FairCallSchedule) (n m b : ℕ) (h p : ℝ)
    (hp : p∈Ioo (0 : ℝ) 1) (hB : S.bits=b) (hP : (S.failure : ℝ)=p)
    (hR : S.level=calibrationPlannerLevel m (h/2)) :
    S.Seed n → CalibrationFairSeed n m b h p hp :=
  transportFairQueryBank hB (scheduledCopyCount_eq S hp hP) hR

lemma scheduledFairSeed_measurePreserving (S : FairCallSchedule) (n m b : ℕ) (h p : ℝ)
    (hp : p∈Ioo (0 : ℝ) 1) (hB : S.bits=b) (hP : (S.failure : ℝ)=p)
    (hR : S.level=calibrationPlannerLevel m (h/2)) :
    MeasurePreserving (scheduledFairSeed S n m b h p hp hB hP hR)
      (fairQueryBankLaw n S.bits (confidenceCopyCount S.failure S.confidence) S.level)
      (calibrationFairSeedLaw n m b h p hp) :=
  transportFairQueryBank_measurePreserving hB (scheduledCopyCount_eq S hp hP) hR

theorem scheduledFairBankCall_value (S : FairCallSchedule) (b : ℕ) (h p : ℝ)
    (hh : h∈Ioo (0 : ℝ) 1) (hp : p∈Ioo (0 : ℝ) 1)
    (hB : S.bits=b) (hH : (S.accuracy : ℝ)=h) (hP : (S.failure : ℝ)=p)
    (hR : S.level=calibrationPlannerLevel m (h/2))
    (y : Fin n → Fin m → ℚ) (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (s : S.Seed n) :
    ((countedRationalFairBankCall y x S.bits S.level S.accuracy S.failure S.confidence s).value : ℝ) =
      calibrationFairCall b h p hp (calibrationRowsCast y) x.1.toFinset (x.2.1 : ℝ) (x.2.2 : ℝ)
        (scheduledFairSeed S n m b h p hp hB hP hR s) := by
  subst b
  subst h
  subst p
  rcases S with ⟨b,R,h,p,Hq⟩
  dsimp only at hR
  subst R
  let Hr := exists_confidence_level hp.1 hp.2
  let cEq := confidenceCopyCount_ratCast p Hq Hr
  let sR : CalibrationFairSeed n m b (h:ℝ) (p:ℝ) hp := fun j c => s j (Fin.cast cEq c)
  have hv := countedRationalFairBankCall_value y x hx b h p hh hp Hq sR
  have hInv : (fun j c => sR j (Fin.cast cEq.symm c))=s := by
    funext j c
    simp only [sR,Fin.cast_cast,Fin.cast_eq_self]
  change ((countedRationalFairBankCall y x b (calibrationPlannerLevel m ((h : ℝ)/2)) h p Hq
    (fun j c => sR j (Fin.cast cEq.symm c))).value : ℝ) =
      calibrationFairCall b (h:ℝ) (p:ℝ) hp (calibrationRowsCast y) x.1.toFinset (x.2.1:ℝ) (x.2.2:ℝ) sR at hv
  rw [hInv] at hv
  have hs : scheduledFairSeed ⟨b,calibrationPlannerLevel m ((h:ℝ)/2),h,p,Hq⟩ n m b (h:ℝ) (p:ℝ)
      hp rfl rfl rfl s=sR := by
    unfold scheduledFairSeed sR
    rw [transportFairQueryBank_copies]
  simpa only [hs] using hv

end ProphetSecretary.Statistics.Calibration
