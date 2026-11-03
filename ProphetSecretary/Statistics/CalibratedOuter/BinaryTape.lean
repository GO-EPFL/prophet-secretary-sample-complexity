import ProphetSecretary.Statistics.CalibratedOuter.BinaryReward
import ProphetSecretary.Statistics.CalibratedOuter.BinarySchedulePolynomial
import ProphetSecretary.Statistics.CalibratedOuter.BinaryExecutable

/-!
# The common fair-bit input for the binary learner

Each planner bank is a view of a disjoint array of primitive bits. Its
layout is computed once and stored with the bank. The rank keys, clock
words, mixture bits, and outer marks already have the required layout.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability ProphetSecretary.Model

private def countedPlannerTape (n b C R : ℕ) (t : PlannerQueryBitTape n b C R) :
    FairQueryBank n b C R × ℕ :=
  countedMultilevelBankFromTape C R (fun i => plannerSeedFromCoordinates n (t i))

private lemma countedPlannerTape_work (n b C R : ℕ) (t : PlannerQueryBitTape n b C R) :
    (countedPlannerTape n b C R t).2≤fairQueryBankWorkBound n b C R := by
  have h := countedMultilevelBankFromTape_work C R (fun i => plannerSeedFromCoordinates n (t i))
  change (countedPlannerTape n b C R t).2≤360*(R+1)^4 at h
  unfold fairQueryBankWorkBound
  omega

variable {n m J b c bT CT RT bP CP RP : ℕ}

private abbrev RankQueryTape (n m J b c bT CT RT bP CP RP : ℕ) :=
  RankCalibrationBits n m J b c (PlannerQueryBitTape n bT CT RT) (PlannerQueryBitTape n bP CP RP)

/-- Decode and store the two kinds of query bank. Every layout is built
once for its own tape. -/
def countedRankQueryTape (t : RankQueryTape n m J b c bT CT RT bP CP RP) :
    RankCalibrationBits n m J b c (FairQueryBank n bT CT RT) (FairQueryBank n bP CP RP) × ℕ :=
  let T := Vector.ofFn (fun i : TargetGrid m => countedPlannerTape n bT CT RT (t.1 i))
  let V := Vector.ofFn (fun j : Fin m => Vector.ofFn (fun k : Fin (n*(J+1)) =>
    countedPlannerTape n bP CP RP ((t.2.1 j).2.2 (finProdFinEquiv.symm k))))
  let O := Vector.ofFn (fun k : Fin (n*(J+1)) =>
    countedPlannerTape n bP CP RP (t.2.2.2.1 (finProdFinEquiv.symm k)))
  let seed := (fun i => (T.get i).1,
    (fun j => ((t.2.1 j).1,(t.2.1 j).2.1, fun k => ((V.get j).get (finProdFinEquiv k)).1)),
    (t.2.2.1,(fun k => (O.get (finProdFinEquiv k)).1),t.2.2.2.2))
  (seed,(∑ i : TargetGrid m, (T.get i).2) +
    (∑ j : Fin m, ∑ k : Fin (n*(J+1)), ((V.get j).get k).2) +
    (∑ k : Fin (n*(J+1)), (O.get k).2) +
    10*((4*m+1)+(m+1)*(n*(J+1))+m+1)+6)

private lemma getVectorOfFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt

lemma countedRankQueryTape_value (t : RankQueryTape n m J b c bT CT RT bP CP RP) :
    (countedRankQueryTape t).1 =
      mapRankCalibrationQueries b c (plannerFairBankFromBitTape n bT CT RT)
        (plannerFairBankFromBitTape n bP CP RP) t := by
  simp only [countedRankQueryTape,mapRankCalibrationQueries,getVectorOfFn,Equiv.symm_apply_apply,
    countedPlannerTape,plannerFairBankFromBitTape]

theorem countedRankQueryTape_work (t : RankQueryTape n m J b c bT CT RT bP CP RP) :
    (countedRankQueryTape t).2 ≤
      (4*m+1)*fairQueryBankWorkBound n bT CT RT+(m+1)*n*(J+1)*fairQueryBankWorkBound n bP CP RP+
      10*((4*m+1)+(m+1)*(n*(J+1))+m+1)+6 := by
  let WT := fairQueryBankWorkBound n bT CT RT
  let WP := fairQueryBankWorkBound n bP CP RP
  have hT : (∑ i : TargetGrid m,(countedPlannerTape n bT CT RT (t.1 i)).2)≤(4*m+1)*WT := by
    calc
      _ ≤ ∑ _i : TargetGrid m,WT := Finset.sum_le_sum (fun i _ => countedPlannerTape_work _ _ _ _ _)
      _ = _ := by simp [TargetGrid]
  have hV (j : Fin m) :
      (∑ k : Fin (n*(J+1)),(countedPlannerTape n bP CP RP ((t.2.1 j).2.2 (finProdFinEquiv.symm k))).2)≤
        n*(J+1)*WP := by
    calc
      _ ≤ ∑ _k : Fin (n*(J+1)),WP := Finset.sum_le_sum (fun k _ => countedPlannerTape_work _ _ _ _ _)
      _ = _ := by simp
  have hVV :
      (∑ j : Fin m, ∑ k : Fin (n*(J+1)),
        (countedPlannerTape n bP CP RP ((t.2.1 j).2.2 (finProdFinEquiv.symm k))).2)≤m*(n*(J+1)*WP) := by
    calc
      _ ≤ ∑ _j : Fin m,n*(J+1)*WP := Finset.sum_le_sum (fun j _ => hV j)
      _ = _ := by simp
  have hO :
      (∑ k : Fin (n*(J+1)),(countedPlannerTape n bP CP RP (t.2.2.2.1 (finProdFinEquiv.symm k))).2)≤
        n*(J+1)*WP := by
    calc
      _ ≤ ∑ _k : Fin (n*(J+1)),WP := Finset.sum_le_sum (fun k _ => countedPlannerTape_work _ _ _ _ _)
      _ = _ := by simp
  simp only [countedRankQueryTape,getVectorOfFn]
  change _≤(4*m+1)*WT+(m+1)*n*(J+1)*WP+10*((4*m+1)+(m+1)*(n*(J+1))+m+1)+6
  rw [show (m+1)*n*(J+1)*WP=m*(n*(J+1)*WP)+n*(J+1)*WP by ring]
  omega

private structure QueryTapeShape where
  grid : ℕ
  clockBits : ℕ
  coinBits : ℕ
  targetBits : ℕ
  targetCopies : ℕ
  targetLevel : ℕ
  policyBits : ℕ
  policyCopies : ℕ
  policyLevel : ℕ

private abbrev QueryTapeShape.Input (q : QueryTapeShape) (n m : ℕ) :=
  RankQueryTape n m q.grid q.clockBits q.coinBits q.targetBits q.targetCopies q.targetLevel
    q.policyBits q.policyCopies q.policyLevel

private abbrev QueryTapeShape.Output (q : QueryTapeShape) (n m : ℕ) :=
  RankCalibrationBits n m q.grid q.clockBits q.coinBits
    (FairQueryBank n q.targetBits q.targetCopies q.targetLevel)
    (FairQueryBank n q.policyBits q.policyCopies q.policyLevel) × ℕ

private def QueryTapeShape.decode (q : QueryTapeShape) (n m : ℕ) (t : q.Input n m) : q.Output n m :=
  countedRankQueryTape t

private theorem QueryTapeShape.decode_cast {q r : QueryTapeShape} (h : q=r) (n m : ℕ) (t : r.Input n m) :
    (congrArg (fun u => u.Output n m) h) ▸ q.decode n m
      ((congrArg (fun u => u.Input n m) h.symm) ▸ t) = r.decode n m t := by
  subst r
  rfl

namespace FairCalibrationParameters

variable {zlo : ℚ}

abbrev NativeOuterTape (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) :=
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  OuterMarkArray n m (Fin (outerMarkBits n m) → Bool) ×
    RankQueryTape n m a.grid a.clockBits a.coinBits T.bits (confidenceCopyCount T.failure T.confidence) T.level
      P.bits (confidenceCopyCount P.failure P.confidence) P.level

set_option synthInstance.maxSize 512 in
instance rankQueryTapeMeasurableSpace : MeasurableSpace (RankQueryTape n m J b c bT CT RT bP CP RP) := by
  unfold RankQueryTape RankCalibrationBits RankCalibrationValidationBits RankCalibrationClockBits
    PolicyQueryArray PlannerQueryBitTape
  infer_instance

noncomputable instance nativeOuterTapeMeasurableSpace (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) :
    MeasurableSpace (a.NativeOuterTape hz) := by
  unfold NativeOuterTape
  dsimp only
  infer_instance

noncomputable def nativeOuterTapeLaw (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) :
    Measure (a.NativeOuterTape hz) :=
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  (Measure.pi fun _ : Fin (outerMarkSlotCount n m) => fairBitVectorLaw (outerMarkBits n m)).prod
    (rankCalibrationBitsLaw a.clockBits a.coinBits
      (plannerQueryBitTapeLaw n T.bits (confidenceCopyCount T.failure T.confidence) T.level)
      (plannerQueryBitTapeLaw n P.bits (confidenceCopyCount P.failure P.confidence) P.level))

noncomputable def countedNativeOuterTape (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo)
    (t : a.NativeOuterTape hz) : a.NativeOuterSeed zlo hz × ℕ :=
  let q := countedRankQueryTape t.2
  ((t.1,q.1),q.2)

private noncomputable def referenceTapeShape (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) :
    QueryTapeShape :=
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  ⟨a.grid,a.clockBits,a.coinBits,T.bits,confidenceCopyCount T.failure T.confidence,T.level,
    P.bits,confidenceCopyCount P.failure P.confidence,P.level⟩

private def executableTapeShape {a : FairCalibrationParameters n m} {z : BinaryRational}
    {hz : (z.value : ℝ)=a.zlo} (q : a.BinaryPublicSetup z hz) (b c : ℕ) : QueryTapeShape :=
  ⟨q.grid,b,c,q.target.bits,2*q.startup.target.halfCopies+1,q.target.level,
    q.threshold.bits,2*q.startup.threshold.halfCopies+1,q.threshold.level⟩

private theorem executableTapeShape_eq {a : FairCalibrationParameters n m} {z : BinaryRational}
    {hz : (z.value : ℝ)=a.zlo} (q : a.BinaryPublicSetup z hz) (b c : ℕ)
    (hb : b=a.clockBits) (hc : c=a.coinBits) :
    executableTapeShape q b c=a.referenceTapeShape hz := by
  unfold executableTapeShape referenceTapeShape confidenceCopyCount
  dsimp only
  rw [q.grid_eq,hb,hc,q.targetCopies,q.thresholdCopies,q.target_eq,q.threshold_eq]

/-- Decode from the sizes computed by binary startup. The type transports
identify these arrays with the reference tape used in the probability law. -/
def countedExecutableOuterTape (a : FairCalibrationParameters n m) (z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (q : a.BinaryPublicSetup z hz) (b c : ℕ)
    (hb : b=a.clockBits) (hc : c=a.coinBits) (t : a.NativeOuterTape hz) :
    a.NativeOuterSeed z.value hz × ℕ :=
  let h := executableTapeShape_eq q b c hb hc
  let u := (executableTapeShape q b c).decode n m
    ((congrArg (fun k : QueryTapeShape => k.Input n m) h.symm) ▸ t.2)
  let r := (congrArg (fun k : QueryTapeShape => k.Output n m) h) ▸ u
  ((t.1,r.1),r.2)

theorem countedExecutableOuterTape_eq (a : FairCalibrationParameters n m) (z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (q : a.BinaryPublicSetup z hz) (b c : ℕ)
    (hb : b=a.clockBits) (hc : c=a.coinBits) (t : a.NativeOuterTape hz) :
    a.countedExecutableOuterTape z hz q b c hb hc t=a.countedNativeOuterTape hz t := by
  exact congrArg (fun r : (a.referenceTapeShape hz).Output n m =>
      (((t.1,r.1),r.2) : a.NativeOuterSeed z.value hz × ℕ))
    (QueryTapeShape.decode_cast (executableTapeShape_eq q b c hb hc) n m t.2)

theorem countedNativeOuterTape_measurePreserving (a : FairCalibrationParameters n m)
    (hz : (zlo : ℝ)=a.zlo) :
    MeasurePreserving (fun t => (a.countedNativeOuterTape hz t).1)
      (a.nativeOuterTapeLaw hz) (a.nativeOuterSeedLaw zlo hz) := by
  let μ := Measure.pi fun _ : Fin (outerMarkSlotCount n m) => fairBitVectorLaw (outerMarkBits n m)
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have h := (MeasurePreserving.id μ).prod (measurePreserving_mapRankCalibrationQueries
    (n := n) (m := m) (J := a.grid) a.clockBits a.coinBits
    (measurePreserving_plannerFairBankFromBitTape n T.bits (confidenceCopyCount T.failure T.confidence) T.level)
    (measurePreserving_plannerFairBankFromBitTape n P.bits (confidenceCopyCount P.failure P.confidence) P.level))
  have he : (fun t : a.NativeOuterTape hz => (a.countedNativeOuterTape hz t).1) =
      Prod.map id (mapRankCalibrationQueries a.clockBits a.coinBits
        (plannerFairBankFromBitTape n T.bits (confidenceCopyCount T.failure T.confidence) T.level)
        (plannerFairBankFromBitTape n P.bits (confidenceCopyCount P.failure P.confidence) P.level)) := by
    funext t
    exact congrArg (fun q => (t.1,q)) (countedRankQueryTape_value t.2)
  rw [he]
  exact h

theorem countedNativeOuterTape_work (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo)
    (t : a.NativeOuterTape hz) :
    (a.countedNativeOuterTape hz t).2≤finiteQueryStorageBound n m a.grid
      a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz) :=
  countedRankQueryTape_work t.2

/-- Number of primitive Boolean entries in the disjoint input arrays. -/
noncomputable def nativeOuterTapeBitCount (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) : ℕ :=
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  (4*m+1)*fairQueryBankBitCount n T.bits (confidenceCopyCount T.failure T.confidence) T.level+
  (m+1)*n*(a.grid+1)*fairQueryBankBitCount n P.bits (confidenceCopyCount P.failure P.confidence) P.level+
  outerMarkSlotCount n m*outerMarkBits n m+n*(2*m+1)*a.clockBits+a.coinBits

theorem nativeOuterTapeBitCount_le (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) :
    a.nativeOuterTapeBitCount hz≤finiteScheduleFairBitsBound n m a.grid a.clockBits a.coinBits
      (outerMarkBits n m) a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz) := by
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  have hT := Nat.mul_le_mul_left (4*m+1)
    (fairQueryBankBitCount_le n T.bits (confidenceCopyCount T.failure T.confidence) T.level)
  have hP := Nat.mul_le_mul_left ((m+1)*n*(a.grid+1))
    (fairQueryBankBitCount_le n P.bits (confidenceCopyCount P.failure P.confidence) P.level)
  unfold nativeOuterTapeBitCount finiteScheduleFairBitsBound
  dsimp only [T,P] at hT hP ⊢
  omega

/-- The primitive tape has exactly one Boolean entry per charged bit. -/
theorem nativeOuterTape_card (a : FairCalibrationParameters n m) (hz : (zlo : ℝ)=a.zlo) :
    Nat.card (a.NativeOuterTape hz)=2^(a.nativeOuterTapeBitCount hz) := by
  have hBool : Nat.card Bool=2 := by simp [Nat.card_eq_fintype_card]
  unfold NativeOuterTape RankQueryTape RankCalibrationBits RankCalibrationValidationBits
    RankCalibrationClockBits TargetGrid PolicyQueryArray OuterMarkArray PlannerQueryBitTape
    nativeOuterTapeBitCount fairQueryBankBitCount
  dsimp only
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,hBool,← pow_mul,← pow_add]
  congr 1
  ring

/-- The executable preparation shares the computed dimensions between
tape decoding and the calibrated controller. -/
def prepareBinaryTapeProgram (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (t : a.NativeOuterTape hz) : a.BinaryPrepared z.value hz × ℕ :=
  let q := a.binaryPublicSetup z hz
  let d := countedBinaryPublicIntegers n m a.clockInverse
  let h := countedBinaryPublicIntegers_value n m a.clockInverse
  let r := a.countedExecutableOuterTape z hz q d.clockBits d.coinBits h.1 h.2.1 t
  (q.prepareAt mu y r.1 d.clockBits d.coinBits d.markBits h.1 h.2.1 h.2.2.1,r.2+q.extraWork+d.work)

theorem prepareBinaryTapeProgram_value (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (t : a.NativeOuterTape hz) :
    (a.prepareBinaryTapeProgram mu z hz y t).1=a.prepareBinaryProgram mu z hz y
      (a.countedNativeOuterTape hz t).1 := by
  unfold prepareBinaryTapeProgram
  dsimp only
  rw [countedExecutableOuterTape_eq]
  exact BinaryPublicSetup.prepareAt_eq _ _ _ _ _ _ _ _ _ _

theorem prepareBinaryTapeProgram_extra_work (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (t : a.NativeOuterTape hz) (D : ℕ) (hD : RationalHeight z.value D) :
    (a.prepareBinaryTapeProgram mu z hz y t).2≤
      finiteQueryStorageBound n m a.grid a.nativeTargetSchedule (a.nativeThresholdSchedule z.value hz)+
        executablePublicSetupExtraBound n m a.grid D+binaryPublicIntegersWork n m a.clockInverse := by
  unfold prepareBinaryTapeProgram
  dsimp only
  rw [countedExecutableOuterTape_eq]
  exact Nat.add_le_add (Nat.add_le_add (a.countedNativeOuterTape_work hz t)
    (a.binaryPublicSetup_extra_work z hz D hD)) (countedBinaryPublicIntegers_work n m a.clockInverse)

def binaryTapeAccepted (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (t : a.NativeOuterTape hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    Finset (Fin n) :=
  let q := (a.prepareBinaryTapeProgram mu z hz (fun i j => BinaryRational.ofRat (y i j)) t).1
  Finset.univ.filter fun i => (a.decideBinaryProgram q (p.symm i) i (BinaryRational.ofRat (x i))
    (encodedRankHistory p x (p.symm i))).1=true

theorem binaryTapeAccepted_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (t : a.NativeOuterTape hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    a.binaryTapeAccepted mu z hz t y x p=a.binaryAccepted mu z hz (a.countedNativeOuterTape hz t).1 y x p := by
  unfold binaryTapeAccepted
  dsimp only
  rw [prepareBinaryTapeProgram_value]
  rfl

open scoped Classical in
noncomputable def binaryTapeReward (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (t : a.NativeOuterTape hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) : ℝ :=
  let A := a.binaryTapeAccepted mu z hz t y x p
  ∑ i : Fin n, if i∈A ∧ (∀ j∈A, p.symm i≤p.symm j) then (x i : ℝ) else 0

theorem binaryTapeReward_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (t : a.NativeOuterTape hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    a.binaryTapeReward mu z hz t y x p=a.binaryReward mu z hz (a.countedNativeOuterTape hz t).1 y x p := by
  unfold binaryTapeReward binaryReward
  dsimp only
  rw [binaryTapeAccepted_eq]

noncomputable def binaryTapeExpectedReward (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (P : RationalOfferInstance n) : ℝ :=
  ∫ w : (Fin n → ℚ) × (Equiv.Perm (Fin n) ×
      ((Fin n → Fin (outerSampleBudget m) → ℚ) × a.NativeOuterTape hz)),
    a.binaryTapeReward mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1
      ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
        ((P.samplesLaw (outerSampleBudget m)).prod (a.nativeOuterTapeLaw hz)))

set_option synthInstance.maxSize 1024 in
theorem binaryTapeExpectedReward_eq (a : FairCalibrationParameters n m) (mu z : BinaryRational)
    (hz : (z.value : ℝ)=a.zlo) (P : RationalOfferInstance n) :
    a.binaryTapeExpectedReward mu z hz P=a.binaryExpectedReward mu z hz P := by
  let L := outerFairRankLearner (by have := a.two_le; omega : 1≤m)
    (a.finiteLearner (mu.value : ℝ)) (outerMarkBits n m)
  let π := L.randomizedPolicy P.toInstance
  let A := (Fin n → ℚ) × (Equiv.Perm (Fin n) ×
    ((Fin n → Fin (outerSampleBudget m) → ℚ) × a.NativeOuterSeed z.value hz))
  let B := (Fin n → ℚ) × (Equiv.Perm (Fin n) ×
    ((Fin n → Fin (outerSampleBudget m) → ℚ) × a.NativeOuterTape hz))
  let μ := P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
    ((P.samplesLaw (outerSampleBudget m)).prod (a.nativeOuterSeedLaw z.value hz)))
  let ν := P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
    ((P.samplesLaw (outerSampleBudget m)).prod (a.nativeOuterTapeLaw hz)))
  let f : A → π.World := fun w =>
    ((fun i => (w.1 i : ℝ)),w.2.1,(fun i j => (w.2.2.1 i j : ℝ)),
      w.2.2.2.1,a.nativeCalibrationBitsToMeasured z.value hz w.2.2.2.2)
  let g : B → A := fun w => (w.1,w.2.1,w.2.2.1,(a.countedNativeOuterTape hz w.2.2.2).1)
  have hS := a.nativeOuterSeed_measurePreserving mu.value z.value hz
  letI : IsProbabilityMeasure (a.nativeOuterSeedLaw z.value hz) := by
    unfold nativeOuterSeedLaw
    infer_instance
  have hf : MeasurePreserving f μ (π.worldLaw P.toInstance) :=
    P.cast_values_measurePreserving.prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
      ((P.cast_samples_measurePreserving _).prod hS))
  letI : IsProbabilityMeasure (a.nativeOuterTapeLaw hz) := ⟨by
    simpa only [Set.preimage_univ,measure_univ] using
      (a.countedNativeOuterTape_measurePreserving hz).measure_preimage
        (s := Set.univ) MeasurableSet.univ.nullMeasurableSet⟩
  have hg : MeasurePreserving g ν μ :=
    (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
      ((MeasurePreserving.id (P.samplesLaw _)).prod (a.countedNativeOuterTape_measurePreserving hz)))
  have he (w : A) :
      a.binaryReward mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1=π.realizedReward (f w) :=
    (a.binaryReward_eq_nativeReward mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1).trans
      (a.nativeReward_eq mu.value z.value hz w.2.2.2 w.2.2.1 w.1 w.2.1)
  unfold binaryTapeExpectedReward
  simp only [binaryTapeReward_eq]
  change (∫ w : B, a.binaryReward mu z hz (g w).2.2.2 (g w).2.2.1 (g w).1 (g w).2.1 ∂ν)=
    ∫ w : A, a.binaryReward mu z hz w.2.2.2 w.2.2.1 w.1 w.2.1 ∂μ
  simp only [he]
  exact hg.hasLaw.integral_comp (π.measurable_realizedReward.comp hf.measurable).aestronglyMeasurable

end FairCalibrationParameters

end ProphetSecretary.Statistics.Calibration
