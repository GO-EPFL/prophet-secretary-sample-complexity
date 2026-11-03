import ProphetSecretary.Statistics.CountedCalibrationPrepare
import ProphetSecretary.Statistics.CountedOnlineCalibration
import ProphetSecretary.Statistics.CalibratedQueryExecution
import ProphetSecretary.Statistics.CalibrationQueryTapes
import ProphetSecretary.Probability.CountedArrivalOrder

/-!
# Work of the arithmetic calibration

The validation profiles store both directions of the arrival order.
The empirical count guard is tested before any scalar query. An online
decision uses only the current arrival and the already observed history.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m J : ℕ}

structure ArithmeticCalibrationScale where
  accuracy : ℝ
  failure : ℝ
  accuracy_mem : accuracy ∈ Ioo (0 : ℝ) 1
  failure_mem : failure ∈ Ioo (0 : ℝ) 1

abbrev ArithmeticCalibrationBank (n m : ℕ) (s : ArithmeticCalibrationScale) :=
  CalibrationPlannerSeed n m s.accuracy s.failure s.failure_mem

noncomputable def arithmeticCalibrationCallBound (n m : ℕ) (s : ArithmeticCalibrationScale) : ℕ :=
  calibrationBankCallBound n m (calibrationPlannerLevel m s.accuracy)
    (confidenceCopyCount s.failure (exists_confidence_level s.failure_mem.1 s.failure_mem.2)) +
      (n+1)^2+3

noncomputable def countedArithmeticCalibrationCall (s : ArithmeticCalibrationScale) (q : Reservoir n m)
    (A : Finset (Fin n)) (u z : ℝ) (tape : ArithmeticCalibrationBank n m s) : ℝ × ℕ :=
  let e := countedRealCalibrationCall s.accuracy s.failure s.accuracy_mem s.failure_mem q A u z tape
  (e.value,e.work)

lemma countedArithmeticCalibrationCall_work [NeZero m] (s : ArithmeticCalibrationScale)
    (q : Reservoir n m) (hc : (totalEmpiricalInstance q).positiveCount ≤ targetCountCutoff m)
    (A : Finset (Fin n)) (u z : ℝ) (tape : ArithmeticCalibrationBank n m s) :
    (countedArithmeticCalibrationCall s q A u z tape).2 ≤ arithmeticCalibrationCallBound n m s :=
  countedRealCalibrationCall_work s.accuracy s.failure s.accuracy_mem s.failure_mem q hc A u z tape

lemma countedArithmeticCalibrationCall_value (s : ArithmeticCalibrationScale) (q : Reservoir n m)
    (A : Finset (Fin n)) (u z : ℝ) (tape : ArithmeticCalibrationBank n m s) :
    (countedArithmeticCalibrationCall s q A u z tape).1 =
      calibrationPlannerCall s.accuracy s.failure s.failure_mem q A u z tape :=
  countedRealCalibrationCall_value s.accuracy s.failure s.accuracy_mem s.failure_mem q A u z tape

private lemma arithmeticCalibrationPositiveCount [NeZero m] (q : Reservoir n m) :
    (∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i) =
      (totalEmpiricalInstance q).positiveCount := by
  rw [← show empiricalPositiveCount (reservoirCoordinates q) = (totalEmpiricalInstance q).positiveCount by
    rw [empiricalPositiveCount_eq]
    unfold trainingInstance
    rw [MeasurableEquiv.symm_apply_apply]]
  simp_rw [countedPlannerProbabilities_ofFn, empiricalPositiveProbability, positiveObservations]
  unfold empiricalPositiveCount
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv, mul_comm, ← Finset.sum_boole]
  rfl

private theorem countedCalibrationPrepare_skip_excess_count [NeZero m]
    {T P : Type} (mu zlo zhi : ℝ) (q : Reservoir n m)
    (hc : ¬ (totalEmpiricalInstance q).positiveCount ≤ targetCountCutoff m)
    (target : ℝ → T → ℝ × ℕ) (estimate : Finset (Fin n) → ℝ → ℝ → P → ℝ × ℕ)
    (r : TargetGrid m → T) (profile : Fin m → CalibrationRankProfile n J ℝ P) :
    countedCalibrationPrepare mu zlo zhi (targetCountCutoff m) target estimate q r profile =
      countedCalibrationPrepare mu zlo zhi (targetCountCutoff m)
        (fun _ _ => (0,0)) (fun _ _ _ _ => (0,0)) q r profile := by
  let L := ∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i
  have hL : targetCountCutoff m < L := by
    rw [show L = (totalEmpiricalInstance q).positiveCount from arithmeticCalibrationPositiveCount q]
    exact lt_of_not_ge hc
  have hTarget : ¬ (L ≤ targetCountCutoff m ∧ mu/2 ≤ (countedEmpiricalMaximum (empiricalStoredRows q)).1) :=
    fun h => hL.not_ge h.1
  have hFallback : decide (targetCountCutoff m < L ∨ 1/4 < (countedEmpiricalMaximum (empiricalStoredRows q)).1) =
      true := decide_eq_true (Or.inl hL)
  dsimp only [L] at hTarget hFallback
  unfold countedCalibrationPrepare
  dsimp only
  simp only [hFallback, countedTargetMinimum, if_neg hTarget, countedRankValidationMemo, if_true]

lemma countedCalibrationPrepare_count_of_active [NeZero m]
    {T P : Type} (mu zlo zhi : ℝ) (q : Reservoir n m)
    (target : ℝ → T → ℝ × ℕ) (estimate : Finset (Fin n) → ℝ → ℝ → P → ℝ × ℕ)
    (r : TargetGrid m → T) (profile : Fin m → CalibrationRankProfile n J ℝ P)
    (h : (countedCalibrationPrepare mu zlo zhi (targetCountCutoff m) target estimate q r profile).fallback = false) :
    (totalEmpiricalInstance q).positiveCount ≤ targetCountCutoff m := by
  by_contra hc
  have hL : targetCountCutoff m <
      ∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i := by
    rw [arithmeticCalibrationPositiveCount q]
    exact lt_of_not_ge hc
  have he : (countedCalibrationPrepare mu zlo zhi (targetCountCutoff m) target estimate q r profile).fallback =
      true := decide_eq_true (Or.inl hL)
  rw [he] at h
  contradiction

def countedArithmeticValidationProfiles {K P : Type} [LinearOrder K]
    (x clocks : Fin m → Fin n → K) (seeds : Fin m → PolicyQueryArray n J P) :
    (Fin m → CalibrationRankProfile n J K P) × ℕ :=
  let t := Vector.ofFn (fun l =>
    let p := countedArrivalOrder (clocks l)
    ((p.1,x l,(fun k => clocks l (p.1 k)),seeds l),p.2+5))
  ((fun l => (t.get l).1),(∑ l : Fin m, (t.get l).2)+4*m+2)

def arithmeticValidationProfilesBound (n m : ℕ) : ℕ := m*(10*(n+1)^2+5)+4*m+2

private lemma arithmeticVectorGet_ofFn {A : Type*} {N : ℕ} (f : Fin N → A) (i : Fin N) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

lemma countedArithmeticValidationProfiles_work {K P : Type} [LinearOrder K]
    (x clocks : Fin m → Fin n → K) (seeds : Fin m → PolicyQueryArray n J P) :
    (countedArithmeticValidationProfiles x clocks seeds).2 ≤ arithmeticValidationProfilesBound n m := by
  have h : ∑ l : Fin m, ((countedArrivalOrder (clocks l)).2+5) ≤ m*(10*(n+1)^2+5) := by
    calc
      _ ≤ ∑ _l : Fin m, (10*(n+1)^2+5) := Finset.sum_le_sum fun l _ =>
        Nat.add_le_add_right (countedArrivalOrder_work _) 5
      _ = _ := by simp
  simp only [countedArithmeticValidationProfiles, arithmeticVectorGet_ofFn, arithmeticValidationProfilesBound]
  omega

structure PreparedArithmeticCalibration (n m J : ℕ) where
  rows : Reservoir n m
  coefficient : ℕ → ℝ
  selected : Fin (J+1)
  fallback : Bool
  work : ℕ

noncomputable def countedArithmeticPrepare (targetScale thresholdScale : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (q : Reservoir n m) (x clocks : Fin m → Fin n → ℝ)
    (banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m targetScale)
      (ArithmeticCalibrationBank n m thresholdScale)) (coin : ℝ) :
    PreparedArithmeticCalibration n m J :=
  let profile := countedArithmeticValidationProfiles x clocks banks.2.1
  let prep := countedCalibrationPrepare mu zlo zhi (targetCountCutoff m)
    (fun z => countedArithmeticCalibrationCall targetScale q Finset.univ 1 z)
    (countedArithmeticCalibrationCall thresholdScale q) q banks.1 profile.1
  ⟨q,storedCalibrationCoefficient J zlo zhi,mixturePolicyIndex J prep.selection coin,prep.fallback,
    prep.work+profile.2+8*(J+1)+10⟩

def arithmeticCalibrationPreparationBound (n m J WT WP : ℕ) : ℕ :=
  100*(n+1)^2*(m+1)^2+26*(n+1)*(m+1)+(4*m+1)*(WT+10)+8+
    m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6)+
    10*(m+1)*(J+3)+8*(J+1)+4*(J+2)+15+
    arithmeticValidationProfilesBound n m+8*(J+1)+10

/-- Bad empirical counts skip both scalar query loops. The bound holds
on every input row array, clock array, and seed outcome. -/
theorem countedArithmeticPrepare_work [NeZero m] (targetScale thresholdScale : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (q : Reservoir n m) (x clocks : Fin m → Fin n → ℝ)
    (banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m targetScale)
      (ArithmeticCalibrationBank n m thresholdScale)) (coin : ℝ) :
    (countedArithmeticPrepare targetScale thresholdScale mu zlo zhi q x clocks banks coin).work ≤
      arithmeticCalibrationPreparationBound n m J
        (arithmeticCalibrationCallBound n m targetScale) (arithmeticCalibrationCallBound n m thresholdScale) := by
  let v := countedArithmeticValidationProfiles x clocks banks.2.1
  let t := fun z => countedArithmeticCalibrationCall targetScale q Finset.univ 1 z
  let p := countedArithmeticCalibrationCall thresholdScale q
  let WT := arithmeticCalibrationCallBound n m targetScale
  let WP := arithmeticCalibrationCallBound n m thresholdScale
  let prep := countedCalibrationPrepare mu zlo zhi (targetCountCutoff m) t p q banks.1 v.1
  have hv : v.2 ≤ arithmeticValidationProfilesBound n m := countedArithmeticValidationProfiles_work _ _ _
  have hw : prep.work ≤
      100*(n+1)^2*(m+1)^2+26*(n+1)*(m+1)+(4*m+1)*(WT+10)+8+
        m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6)+
        10*(m+1)*(J+3)+8*(J+1)+4*(J+2)+15 := by
    by_cases hc : (totalEmpiricalInstance q).positiveCount ≤ targetCountCutoff m
    · exact countedCalibrationPrepare_work mu zlo zhi (targetCountCutoff m) t p q banks.1 v.1 WT WP
        (fun _ _ => countedArithmeticCalibrationCall_work _ _ hc _ _ _ _)
        (fun _ _ _ _ => countedArithmeticCalibrationCall_work _ _ hc _ _ _ _)
    · dsimp only [prep]
      rw [countedCalibrationPrepare_skip_excess_count mu zlo zhi q hc t p banks.1 v.1]
      exact countedCalibrationPrepare_work mu zlo zhi (targetCountCutoff m) (fun _ _ => (0,0))
        (fun _ _ _ _ => (0,0)) q banks.1 v.1 WT WP (fun _ _ => Nat.zero_le _)
        (fun _ _ _ _ => Nat.zero_le _)
  change prep.work+v.2+8*(J+1)+10 ≤ _
  unfold arithmeticCalibrationPreparationBound
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hw hv) _) _

noncomputable def countedArithmeticDecision (thresholdScale : ArithmeticCalibrationScale)
    (p : PreparedArithmeticCalibration n m J) (t x : ℝ) (H : History n) (i : Fin n)
    (r : PolicyQueryArray n J (ArithmeticCalibrationBank n m thresholdScale)) : Bool × ℕ :=
  countedOnlineCalibrationDecision p.coefficient (countedArithmeticCalibrationCall thresholdScale p.rows)
    p.rows p.fallback p.selected t x H i r

def arithmeticCalibrationArrivalBound (n m J WP : ℕ) : ℕ := n*(m+4)+10+(J+1)*(WP+2)

theorem countedArithmeticDecision_work [NeZero m] (targetScale thresholdScale : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (q : Reservoir n m) (x clocks : Fin m → Fin n → ℝ)
    (banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m targetScale)
      (ArithmeticCalibrationBank n m thresholdScale)) (coin t offer : ℝ) (H : History n) (i : Fin n) :
    (countedArithmeticDecision thresholdScale
      (countedArithmeticPrepare targetScale thresholdScale mu zlo zhi q x clocks banks coin)
        t offer H i banks.2.2).2 ≤
      arithmeticCalibrationArrivalBound n m J (arithmeticCalibrationCallBound n m thresholdScale) := by
  let prep := countedArithmeticPrepare targetScale thresholdScale mu zlo zhi q x clocks banks coin
  let WP := arithmeticCalibrationCallBound n m thresholdScale
  change (countedArithmeticDecision thresholdScale prep t offer H i banks.2.2).2 ≤ _
  by_cases hf : prep.fallback = true
  · simp only [countedArithmeticDecision, countedOnlineCalibrationDecision, hf, if_true,
      arithmeticCalibrationArrivalBound]
    omega
  · have hfalse : prep.fallback = false := Bool.eq_false_iff.mpr hf
    have hc : (totalEmpiricalInstance q).positiveCount ≤ targetCountCutoff m :=
      countedCalibrationPrepare_count_of_active mu zlo zhi q
        (fun z => countedArithmeticCalibrationCall targetScale q Finset.univ 1 z)
        (countedArithmeticCalibrationCall thresholdScale q) banks.1
        (countedArithmeticValidationProfiles x clocks banks.2.1).1 hfalse
    exact countedOnlineCalibrationDecision_work_le _ _ _ _ _ _ _ _ _ _ WP
      (fun _ _ _ _ => countedArithmeticCalibrationCall_work thresholdScale q hc _ _ _ _)

/-- A stopped execution uses at most one online decision for each
identity. The history and time supplied to each call can be arbitrary. -/
theorem countedArithmeticTotalWork [NeZero m] (targetScale thresholdScale : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (q : Reservoir n m) (x clocks : Fin m → Fin n → ℝ)
    (banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m targetScale)
      (ArithmeticCalibrationBank n m thresholdScale)) (coin : ℝ) (S : Finset (Fin n))
    (t offer : Fin n → ℝ) (H : Fin n → History n) :
    let prep := countedArithmeticPrepare targetScale thresholdScale mu zlo zhi q x clocks banks coin
    let WT := arithmeticCalibrationCallBound n m targetScale
    let WP := arithmeticCalibrationCallBound n m thresholdScale
    prep.work + (∑ i ∈ S, (countedArithmeticDecision thresholdScale prep (t i) (offer i) (H i) i banks.2.2).2) ≤
      arithmeticCalibrationPreparationBound n m J WT WP + n*arithmeticCalibrationArrivalBound n m J WP := by
  dsimp only
  apply Nat.add_le_add (countedArithmeticPrepare_work _ _ _ _ _ _ _ _ _ _)
  let WP := arithmeticCalibrationCallBound n m thresholdScale
  let W := arithmeticCalibrationArrivalBound n m J WP
  calc
    _ ≤ ∑ _i ∈ S, W := Finset.sum_le_sum fun i _ =>
      countedArithmeticDecision_work _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ = S.card*W := by simp
    _ ≤ _ := Nat.mul_le_mul_right W (S.card_le_univ.trans_eq (Fintype.card_fin n))

end ProphetSecretary.Statistics.Calibration
