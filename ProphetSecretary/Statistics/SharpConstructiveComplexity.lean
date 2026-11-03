import ProphetSecretary.Statistics.CalibratedOuter.ArithmeticProgram
import ProphetSecretary.Statistics.ConstructiveSampleBounds
import ProphetSecretary.Statistics.ArithmeticLearningTotal

/-!
# Sharp sample complexity and polynomial arithmetic time

A single choice of the public calibration parameters works for all finite
instance sizes. The upper budget is enforced on every sample transcript,
while the competitive guarantee averages the training and online runs.
-/

open Set
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis
open ProphetSecretary.Statistics.Calibration

noncomputable def arithmeticCallCopies (s : ArithmeticCalibrationScale) : ℕ :=
  confidenceCopyCount s.failure (exists_confidence_level s.failure_mem.1 s.failure_mem.2)

noncomputable def arithmeticCallLevel (m : ℕ) (s : ArithmeticCalibrationScale) : ℕ :=
  calibrationPlannerLevel m s.accuracy

/-- Includes allocation for every possible query slot, even if that slot
is skipped by a guard or by stopping early. -/
noncomputable def arithmeticOuterHardWork (n m : ℕ) (hn : 0<n) (hm : 2≤m) (zlo : ℝ)
    (hz : zlo∈Ioo (0 : ℝ) (1/4)) : ℕ :=
  let J := familyGridSize m zlo (1/4)
  let T := arithmeticTargetScale m hm
  let P := arithmeticThresholdScale n m J hn hm zlo hz
  outerArithmeticOverhead n m+1000*(n+m+2)^4+
    arithmeticCalibrationAuxBound n m J (arithmeticCallCopies T) (arithmeticCallLevel m T)
      (arithmeticCallCopies P) (arithmeticCallLevel m P)+
    arithmeticCalibrationTotalBound n m J (arithmeticCalibrationCallBound n m T)
      (arithmeticCalibrationCallBound n m P)

noncomputable def outerArithmeticWorkConstant (zlo : ℝ) : ℝ :=
  10000001000+500*(calibrationWorkConstant zlo+1)

/-- The hard budget covers the actual allocator, preparer, and reached
online decisions, as well as the full sample read and outer marks. -/
theorem arithmeticOuterSchedule_work_le {n m : ℕ} [NeZero m] (hn : 0<n) (hm : 2≤m)
    (mu zlo : ℝ) (hz : zlo∈Ioo (0 : ℝ) (1/4)) :
    let J := familyGridSize m zlo (1/4)
    let T := arithmeticTargetScale m hm
    let P := arithmeticThresholdScale n m J hn hm zlo hz
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo (1/4)
    ∀ (p : OuterLearnerInput m L) (S : Finset (Fin n)) (t x : Fin n → ℝ) (H : Fin n → History n)
      (uniform : StateM ℕ ℝ) (sample : Fin n → StateM ℕ ℝ) (c : ℕ),
      let q := prepareArithmeticOuter J (by omega) T P mu zlo (1/4) p
      let alloc := sampleArithmeticCalibrationAuxM n m J (arithmeticCallCopies T) (arithmeticCallLevel m T)
        (arithmeticCallCopies P) (arithmeticCallLevel m P) uniform
      let slots := outerMarkSlotCount n m
      ((countedFullSamplesM n (outerSampleBudget m) sample).run c).1.2+
        ((sampleOuterMarksM n m uniform).run c).1.2+slots+
        ((alloc.run c).1.work)+q.work+
        (∑ i ∈ S, (decideArithmeticOuter P q (outerOnlineTags m L p) (t i) i (x i) (H i)).2)+
        (countedCalibrationGridSize m zlo (1/4)).2 ≤ arithmeticOuterHardWork n m hn hm zlo hz := by
  dsimp only
  intro p S t x H uniform sample c
  let J := familyGridSize m zlo (1/4)
  let T := arithmeticTargetScale m hm
  let P := arithmeticThresholdScale n m J hn hm zlo hz
  let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo (1/4)
  have hD := arithmeticOuterDecisionWork J (by omega) T P mu zlo (1/4) p
    (outerOnlineTags m L p) S t x H
  dsimp only at hD
  have hA := sampleArithmeticCalibrationAuxM_work n m J (arithmeticCallCopies T) (arithmeticCallLevel m T)
    (arithmeticCallCopies P) (arithmeticCallLevel m P) uniform c
  have hG := countedCalibrationGridSize_work m zlo (1/4)
  let N := n+m+2
  have hmN : m≤N^4 := by
    have h : N^1≤N^4 := Nat.pow_le_pow_right (by dsimp [N]; omega) (by decide)
    rw [pow_one] at h
    exact (show m≤N by dsimp [N]; omega).trans h
  have hOne : 1≤N^4 := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  rw [countedFullSamplesM_work,sampleOuterMarksM_work]
  unfold arithmeticOuterHardWork outerArithmeticOverhead arithmeticCalibrationTotalBound
  dsimp only
  change _ ≤ _+1000*N^4+_+_
  unfold outerPreparationWorkBound at hD
  dsimp only [J,T,P,L] at hD hA
  have hSlots : 4*(outerMarkSlotCount n m+1)+outerMarkSlotCount n m≤5*(outerMarkSlotCount n m+1) := by omega
  omega

theorem arithmeticOuterHardWork_polynomial (n m : ℕ) (hn : 0<n) (hm : 2≤m) (zlo : ℝ)
    (hz : zlo∈Ioo (0 : ℝ) (1/4)) :
    (arithmeticOuterHardWork n m hn hm zlo hz : ℝ)≤
      outerArithmeticWorkConstant zlo*((n : ℝ)+m+2)^295 := by
  letI : NeZero m := ⟨by omega⟩
  let N := (n : ℝ)+m+2
  let J := familyGridSize m zlo (1/4)
  have hJ : J≤m := familyGridSize_le (by linarith [hz.1])
  let T := arithmeticTargetScale m hm
  let P := arithmeticThresholdScale n m J hn hm zlo hz
  let A := calibrationWorkConstant zlo
  have hA : 0≤A := by unfold A calibrationWorkConstant; positivity
  have hT : (calibrationFullQueryBound n m (arithmeticCallLevel m T) (arithmeticCallCopies T) : ℝ)≤A*N^291 :=
    calibrationTargetQueryWork_polynomial hm hz.1 _
  have hP : (calibrationFullQueryBound n m (arithmeticCallLevel m P) (arithmeticCallCopies P) : ℝ)≤A*N^291 :=
    calibrationThresholdQueryWork_polynomial hn hm hJ hz _
  have hT' : (arithmeticCalibrationCallBound n m T : ℝ)≤A*N^291 := by
    have h := arithmeticCalibrationCallBound_le_full n m T
    exact (by exact_mod_cast h : (arithmeticCalibrationCallBound n m T : ℝ)≤
      calibrationFullQueryBound n m (arithmeticCallLevel m T) (arithmeticCallCopies T)).trans hT
  have hP' : (arithmeticCalibrationCallBound n m P : ℝ)≤A*N^291 := by
    have h := arithmeticCalibrationCallBound_le_full n m P
    exact (by exact_mod_cast h : (arithmeticCalibrationCallBound n m P : ℝ)≤
      calibrationFullQueryBound n m (arithmeticCallLevel m P) (arithmeticCallCopies P)).trans hP
  have hCal := arithmeticCalibrationTotalBound_of_query_bounds n m J
    (arithmeticCalibrationCallBound n m T) (arithmeticCalibrationCallBound n m P) hJ A hT' hP'
  have hAux := arithmeticCalibrationAuxBound_polynomial hJ hA hT hP
  have hOver : (outerArithmeticOverhead n m : ℝ)≤10000000000*N^3 := by
    dsimp [N]
    exact_mod_cast outerArithmeticOverhead_poly n m
  have hN : 1≤N := by
    dsimp [N]
    linarith only [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
  have h3 : N^3≤N^295 := pow_le_pow_right₀ hN (by decide)
  have h4 : N^4≤N^295 := pow_le_pow_right₀ hN (by decide)
  unfold arithmeticOuterHardWork
  push_cast
  calc
    _ ≤ 10000000000*N^295+1000*N^295+100*(A+1)*N^295+400*(A+1)*N^295 :=
      add_le_add (add_le_add (add_le_add (hOver.trans (mul_le_mul_of_nonneg_left h3 (by norm_num)))
        (mul_le_mul_of_nonneg_left h4 (by norm_num))) hAux) hCal
    _ = _ := by unfold outerArithmeticWorkConstant; rw [← add_mul,← add_mul,← add_mul]; congr 1; dsimp only [A]; ring

/-- The public scales in the schedule are exactly those of the learner
in the statistical outer guarantee. -/
theorem arithmeticOuterLearner_eq_for_scales {n m : ℕ} [NeZero m]
    (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (hn : 0<n) (hm : 2≤m) :
    let zlo := (1-(b : ℝ))/(b : ℝ)
    let J := familyGridSize m zlo (1/4)
    let L := arithmeticLearnerForScales (n := n) (m := m) J (arithmeticTargetScale m hm)
      (arithmeticThresholdScale n m J hn hm zlo (calibrationEndpoint_coefficient_bounds hb))
      (1/10000000) zlo (1/4)
    arithmeticOuterLearner b hb n m (by omega) = computedOuterLearner m (by omega) L := by
  dsimp only
  unfold arithmeticOuterLearner arithmeticCalibratedLearner
  rw [dif_pos ⟨hn,hm⟩]
  rfl

/-- Paper label `thm:theta-main`. The sample lower bound applies to
arbitrary adaptive training requests. The arithmetic upper bound uses the
actual calibrated program and fixes its constants before the unknown laws. -/
theorem sharp_sample_complexity_and_polynomial_time :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (a A eps0 : ℝ) (d : ℕ),
      0<a ∧ a≤A ∧ 0<eps0 ∧ ∀ eps∈Ioo (0 : ℝ) eps0,
        (∃ (m : ℕ) (hm : 2≤m), (outerSampleBudget m : ℝ)≤A/eps ∧
          (∀ n : ℕ, (arithmeticOuterLearner b hb n m (by omega)).Guarantees
            (optimalCompetitiveRatio-eps)) ∧
          (∀ (n : ℕ) (hn : 0<n),
            (arithmeticOuterHardWork n m hn hm ((1-(b : ℝ))/(b : ℝ))
              (calibrationEndpoint_coefficient_bounds hb) : ℝ)≤A*((n : ℝ)+1/eps)^d)) ∧
        ∀ k : ℕ, FeasibleBudget eps k → a/eps≤(k : ℝ) := by
  obtain ⟨a,η,ha,hη,hLow⟩ := LowerBound.sample_lower_bound
  obtain ⟨b,hb,K,hK,hUpper⟩ := exists_arithmetic_outer_learner
  let C := optimalCompetitiveRatio
  let D := outerReductionLocalConstant K+3*C
  let S := outerRequiredScale K
  let zlo := (1-(b : ℝ))/(b : ℝ)
  have hz := calibrationEndpoint_coefficient_bounds hb
  have hD : 0<D := by
    have hC := half_le_optimalCompetitiveRatio
    have hR := outerReductionLocalConstant_nonneg hK.le
    dsimp [D,C]
    linarith only [hC,hR]
  have hS : 0<S := by dsimp [S,outerRequiredScale]; omega
  have hSR : (0 : ℝ)<S := by exact_mod_cast hS
  let A := max a (max (4*(D+1)) (outerArithmeticWorkConstant zlo*(D+3)^295))
  let eps0 := min η (min 1 (D/(S : ℝ)))
  refine ⟨b,hb,a,A,eps0,295,ha,le_max_left _ _,
    lt_min hη (lt_min zero_lt_one (div_pos hD hSR)),?_⟩
  intro eps he
  have he0 := he.1
  have he1 : eps<1 := (he.2.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have heS : eps<D/(S : ℝ) := (he.2.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  let m := ⌈D/eps⌉₊
  have hmD : D/eps≤(m : ℝ) := Nat.le_ceil _
  have hmS : S≤m := by
    have h := ((lt_div_iff₀ he0).mpr (by
      simpa only [mul_comm] using (lt_div_iff₀ hSR).mp heS)).le.trans hmD
    exact_mod_cast h
  have hmBig : 2000000000≤m := by dsimp [S,outerRequiredScale] at hmS; omega
  have hm2 : 2≤m := by omega
  have hm0 : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hCeil : (m : ℝ)≤D/eps+1 := (Nat.ceil_lt_add_one (div_nonneg hD.le he0.le)).le
  have hBudget := outerSampleBudget_le_four_mul m hmBig
  have hCount : (outerSampleBudget m : ℝ)≤4*(D+1)/eps := by
    calc
      _ ≤ 4*(m : ℝ) := by exact_mod_cast hBudget
      _ ≤ 4*(D/eps+1) := mul_le_mul_of_nonneg_left hCeil (by norm_num)
      _ ≤ _ := by
        apply (le_div_iff₀ he0).mpr
        have h : 4*(D/eps+1)*eps=4*(D+eps) := by field_simp
        rw [h]
        linarith only [he1]
  have hErr : D/(m : ℝ)≤eps := (div_le_iff₀ hm0).mpr (by
    simpa only [mul_comm] using (div_le_iff₀ he0).mp hmD)
  refine ⟨⟨m,hm2,hCount.trans (div_le_div_of_nonneg_right
    ((le_max_left (4*(D+1)) _).trans (le_max_right a _)) he0.le),?_,?_⟩,?_⟩
  · intro n P hP
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hErr C)
      P.expectedMaximum_nonnegative).trans (hUpper n m hmS P hP)
  · intro n hn
    let N := (n : ℝ)+m+2
    let Q := (n : ℝ)+1/eps
    have hScale : N≤(D+3)*Q := by
      have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
      have hinv : (1 : ℝ)≤1/eps := (le_div_iff₀ he0).mpr (by linarith only [he1])
      have h1 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ)≤3)
      have h2 := mul_nonneg (by linarith only [hD] : 0≤D+2) hn0
      dsimp only [N,Q]
      nlinarith only [hCeil,h1,h2,show D/eps=D*(1/eps) by ring]
    have hW : 0≤outerArithmeticWorkConstant zlo := by
      unfold outerArithmeticWorkConstant calibrationWorkConstant
      positivity
    calc
      _ ≤ outerArithmeticWorkConstant zlo*N^295 := arithmeticOuterHardWork_polynomial n m hn hm2 zlo hz
      _ ≤ outerArithmeticWorkConstant zlo*((D+3)*Q)^295 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by dsimp [N]; positivity) hScale _) hW
      _ = (outerArithmeticWorkConstant zlo*(D+3)^295)*Q^295 := by rw [mul_pow, mul_assoc]
      _ ≤ A*Q^295 := mul_le_mul_of_nonneg_right
        ((le_max_right (4*(D+1)) _).trans (le_max_right a _)) (by dsimp [Q]; positivity)
  · intro k hk
    exact hLow eps ⟨he0,he.2.trans_le (min_le_left _ _)⟩ k hk

end ProphetSecretary.Statistics
