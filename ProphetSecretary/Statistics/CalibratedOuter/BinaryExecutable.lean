import ProphetSecretary.Statistics.CalibratedOuter.BinaryProgram
import ProphetSecretary.Statistics.BinaryPublicGrid
import ProphetSecretary.Statistics.BinaryPublicIntegers

/-!
# Executable public setup and learner preparation

The natural grid size and the query descriptors are computed in binary.
Equalities with the mathematical descriptors transport only the types of
the seed arrays; no measured or exact-real operation is performed.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ}

private def encodedNumerator (x : BinaryRational) : ℤ :=
  let k := binaryWordValue x.storage.numerator
  if x.storage.negative then -(k : ℤ) else k

private lemma encodedNumerator_eq (x : BinaryRational) : encodedNumerator x=x.value.num := by
  have hs : x.storage=BinaryFraction.encode x.value := x.canonical
  unfold encodedNumerator
  rw [hs]
  dsimp only [BinaryFraction.encode]
  rw [binaryWordValue_bits]
  by_cases h : x.value.num<0
  · simp only [h,decide_true,ite_true]
    have e := Int.natAbs_of_nonneg (Int.neg_nonneg.mpr h.le)
    rw [Int.natAbs_neg] at e
    omega
  · simp only [h,decide_false,Bool.false_eq_true,ite_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

private lemma encodedDenominator_eq (x : BinaryRational) :
    binaryWordValue x.storage.denominator=x.value.den := by
  have hs : x.storage=BinaryFraction.encode x.value := x.canonical
  rw [hs]
  exact binaryWordValue_bits _

/-- Repack the already reduced words without rational normalization. -/
private def repackEncoded (x : BinaryRational) : ℚ :=
  ⟨encodedNumerator x,binaryWordValue x.storage.denominator,
    by rw [encodedDenominator_eq]; exact x.value.den_nz,
    by rw [encodedNumerator_eq,encodedDenominator_eq]; exact x.value.reduced⟩

private lemma repackEncoded_eq (x : BinaryRational) : repackEncoded x=x.value := by
  apply Rat.ext <;> first | exact encodedNumerator_eq x | exact encodedDenominator_eq x

private def repackEncodedWork (x : BinaryRational) : ℕ :=
  15*(max x.storage.numerator.length x.storage.denominator.length+2)^2

private lemma repackEncodedWork_le (x : BinaryRational) (B : ℕ) (hx : RationalHeight x.value B) :
    repackEncodedWork x≤15*(B+3)^2 := by
  unfold repackEncodedWork
  have hw := x.storage_width B hx
  change max x.storage.numerator.length x.storage.denominator.length≤B+1 at hw
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private def binaryCallSchedule (q : BinaryPublicSearchResult) (h p : BinaryRational)
    (hp : ∃ j : ℕ, (1/4 : ℚ)^j≤p.value) : FairCallSchedule :=
  ⟨q.precision,q.level,repackEncoded h,repackEncoded p,(repackEncoded_eq p).symm ▸ hp⟩

private lemma binaryCallSchedule_eq (q : BinaryPublicSearchResult) (h p : BinaryRational)
    (hp : ∃ j : ℕ, (1/4 : ℚ)^j≤p.value) (s : FairCallSchedule)
    (hb : q.precision=s.bits) (hr : q.level=s.level) (hh : h.value=s.accuracy)
    (hf : p.value=s.failure) : binaryCallSchedule q h p hp=s := by
  obtain ⟨b,R,a,f,H⟩ := s
  change q.precision=b at hb
  change q.level=R at hr
  change h.value=a at hh
  change p.value=f at hf
  subst b R a f
  have hExt (u v u' v' : ℚ)
      (hu : u=u') (hv : v=v') (huv : ∃ j : ℕ, (1/4 : ℚ)^j≤v)
      (huv' : ∃ j : ℕ, (1/4 : ℚ)^j≤v') :
      (⟨q.precision,q.level,u,v,huv⟩ : FairCallSchedule)=
        ⟨q.precision,q.level,u',v',huv'⟩ := by
    subst u' v'
    rfl
  exact hExt _ _ _ _ (repackEncoded_eq h) (repackEncoded_eq p) _ _


namespace FairCalibrationParameters

structure BinaryPublicSetup (a : FairCalibrationParameters n m) (z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) where
  grid : ℕ
  target : FairCallSchedule
  threshold : FairCallSchedule
  startup : BinaryLearnerStartup
  grid_eq : grid=a.grid
  target_eq : target=a.nativeTargetSchedule
  threshold_eq : threshold=a.nativeThresholdSchedule z.value hz
  startup_eq : startup=countedBinaryLearnerStartup n m grid z
  targetCopies : startup.target.halfCopies=(countedConfidenceLevel target.failure target.confidence).1
  thresholdCopies : startup.threshold.halfCopies=(countedConfidenceLevel threshold.failure threshold.confidence).1
  extraWork : ℕ
  extraWork_eq : extraWork=(countedBinaryPublicGrid m z).2+
    repackEncodedWork (startup.inputs 1)+repackEncodedWork (startup.inputs 2)+
    repackEncodedWork (startup.inputs 3)+repackEncodedWork (startup.inputs 4)+8

def binaryPublicSetup (a : FairCalibrationParameters n m) (z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) : a.BinaryPublicSetup z hz := by
  let g := countedBinaryPublicGrid m z
  let J := g.1
  have hJ : J=a.grid := (countedBinaryPublicGrid_value m z).trans (a.rationalGrid_eq z.value hz)
  let q := countedBinaryLearnerStartup n m J z
  have hq : q=countedBinaryLearnerStartup n m a.grid z := congrArg (fun j => countedBinaryLearnerStartup n m j z) hJ
  have h := countedBinaryLearnerStartup_value a z hz
  dsimp only at h
  rw [← hq] at h
  have hfT : (q.inputs 2).value=a.nativeTargetSchedule.failure := by
    change (q.inputs 2).value=rationalTargetFailure m
    exact (countedBinaryCalibrationQueryInputs_value n m J z).2.2.1
  have hfP : (q.inputs 4).value=(a.nativeThresholdSchedule z.value hz).failure := by
    change (q.inputs 4).value=rationalThresholdFailure n m (rationalFamilyGridSize m z.value (1/4))
    rw [← countedBinaryPublicGrid_value m z]
    exact (countedBinaryCalibrationQueryInputs_value n m J z).2.2.2.2
  let T := binaryCallSchedule q.target (q.inputs 1) (q.inputs 2) (hfT.symm ▸ a.nativeTargetSchedule.confidence)
  let P := binaryCallSchedule q.threshold (q.inputs 3) (q.inputs 4)
    (hfP.symm ▸ (a.nativeThresholdSchedule z.value hz).confidence)
  have hT : T=a.nativeTargetSchedule := binaryCallSchedule_eq _ _ _ _ _ h.2.2.2.1 h.2.2.1 h.1 hfT
  have hP : P=a.nativeThresholdSchedule z.value hz :=
    binaryCallSchedule_eq _ _ _ _ _ h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 h.2.1 hfP
  exact ⟨J,T,P,q,hJ,hT,hP,rfl,by rw [hT]; exact h.2.2.2.2.1,
    by rw [hP]; exact h.2.2.2.2.2.2.2,g.2+repackEncodedWork (q.inputs 1)+repackEncodedWork (q.inputs 2)+
      repackEncodedWork (q.inputs 3)+repackEncodedWork (q.inputs 4)+8,rfl⟩

def BinaryPublicSetup.prepareAt {a : FairCalibrationParameters n m} {z : BinaryRational}
    {hz : (z.value : ℝ)=a.zlo} (q : a.BinaryPublicSetup z hz) (mu : BinaryRational)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (seed : a.NativeOuterSeed z.value hz) (b c o : ℕ)
    (hb : b=a.clockBits) (hc : c=a.coinBits) (ho : o=outerMarkBits n m) : a.BinaryPrepared z.value hz :=
  let bits : RankCalibrationBits n m q.grid b c (q.target.Seed n) (q.threshold.Seed n) :=
    cast (by rw [q.grid_eq,q.target_eq,q.threshold_eq,hb,hc]) seed.2
  let marks : OuterMarkArray n m (Fin o → Bool) := cast (by rw [ho]) seed.1
  let p := countedBinaryLearnerPrepare (by have := a.two_le; omega) q.target q.threshold
    q.startup.target.halfCopies q.startup.threshold.halfCopies q.targetCopies q.thresholdCopies
    mu z (BinaryRational.ofRat (1/4)) (q.startup.inputs 1) (q.startup.inputs 3)
    b c o y marks bits
  ⟨q.grid,q.threshold,p,q.startup.inputs 3,q.startup.threshold.halfCopies,q.thresholdCopies,
    q.startup.work+p.work+3⟩

theorem BinaryPublicSetup.prepareAt_eq {a : FairCalibrationParameters n m} {z : BinaryRational}
    {hz : (z.value : ℝ)=a.zlo} (q : a.BinaryPublicSetup z hz) (mu : BinaryRational)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational) (seed : a.NativeOuterSeed z.value hz)
    (b c o : ℕ) (hb : b=a.clockBits) (hc : c=a.coinBits) (ho : o=outerMarkBits n m) :
    q.prepareAt mu y seed b c o hb hc ho=a.prepareBinaryProgram mu z hz y seed := by
  subst b c o
  obtain ⟨J,T,P,s,hJ,hT,hP,hs,hct,hcp,w,hw⟩ := q
  subst J T P s
  rfl

/-- Public setup and preparation of the learner on encoded observations.
The extra counter charges for the coefficient grid, descriptor repacking,
and public integer scales. -/
def prepareExecutableBinaryProgram (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational) (seed : a.NativeOuterSeed z.value hz) :
    a.BinaryPrepared z.value hz × ℕ :=
  let q := a.binaryPublicSetup z hz
  let d := countedBinaryPublicIntegers n m a.clockInverse
  let h := countedBinaryPublicIntegers_value n m a.clockInverse
  (q.prepareAt mu y seed d.clockBits d.coinBits d.markBits h.1 h.2.1 h.2.2.1,q.extraWork+d.work)

theorem prepareExecutableBinaryProgram_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational) (seed : a.NativeOuterSeed z.value hz) :
    (a.prepareExecutableBinaryProgram mu z hz y seed).1=a.prepareBinaryProgram mu z hz y seed := by
  let h := countedBinaryPublicIntegers_value n m a.clockInverse
  exact (a.binaryPublicSetup z hz).prepareAt_eq mu y seed _ _ _ h.1 h.2.1 h.2.2.1

def executablePublicSetupExtraBound (n m J D : ℕ) : ℕ :=
  binaryPublicGridWork (m+D+2)+60*(binaryLearnerAccuracyWidth n m J D+3)^2+8

theorem binaryPublicSetup_extra_work (a : FairCalibrationParameters n m) (z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (D : ℕ) (hD : RationalHeight z.value D) :
    (a.binaryPublicSetup z hz).extraWork≤executablePublicSetupExtraBound n m a.grid D := by
  let q := a.binaryPublicSetup z hz
  have h := countedBinaryLearnerStartup_bounds n m a.grid D z hD
  let B := binaryLearnerAccuracyWidth n m a.grid D
  have H (i : Fin 5) : RationalHeight (q.startup.inputs i).value B := by
    rw [q.startup_eq,q.grid_eq]
    exact h.1 i
  have h1 := repackEncodedWork_le (q.startup.inputs 1) B (H 1)
  have h2 := repackEncodedWork_le (q.startup.inputs 2) B (H 2)
  have h3 := repackEncodedWork_le (q.startup.inputs 3) B (H 3)
  have h4 := repackEncodedWork_le (q.startup.inputs 4) B (H 4)
  have hG := countedBinaryPublicGrid_work m D z hD
  change q.extraWork≤_
  rw [q.extraWork_eq]
  change _≤binaryPublicGridWork (m+D+2)+60*(B+3)^2+8
  omega

theorem prepareExecutableBinaryProgram_extra_work (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (seed : a.NativeOuterSeed z.value hz) (D : ℕ) (hD : RationalHeight z.value D) :
    (a.prepareExecutableBinaryProgram mu z hz y seed).2≤executablePublicSetupExtraBound n m a.grid D+
      binaryPublicIntegersWork n m a.clockInverse :=
  Nat.add_le_add (a.binaryPublicSetup_extra_work z hz D hD) (countedBinaryPublicIntegers_work n m a.clockInverse)

end FairCalibrationParameters
end ProphetSecretary.Statistics.Calibration
