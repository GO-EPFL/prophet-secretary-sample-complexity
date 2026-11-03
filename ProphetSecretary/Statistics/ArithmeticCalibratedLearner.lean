import ProphetSecretary.Statistics.CalibratedScalarCalls
import ProphetSecretary.Statistics.CalibratedPlannerGuarantee
import ProphetSecretary.Statistics.CalibratedOuter.SampleUpperBound

/-!
# The arithmetic calibrated learner and its outer guarantee

The target and continuation callbacks below are the same recursive scalar
estimator with the two tolerances specified in the calibrated construction.
The bounded learner's reward and reach are then available to the
distribution-free outer reduction.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

lemma targetAccuracy_mem {m : ℕ} (hm : 2≤m) :
    1/(m : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

lemma targetFailure_mem {m : ℕ} (hm : 2≤m) :
    1/((m : ℝ)^2*(4*(m : ℝ)+1)) ∈ Ioo (0 : ℝ) 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) < (m : ℝ)^2*(4*(m : ℝ)+1) := by
    calc
      (1 : ℝ) < 4*9 := by norm_num
      _ ≤ _ := mul_le_mul (by nlinarith) (by linarith) (by norm_num) (by positivity)
  exact ⟨one_div_pos.mpr (zero_lt_one.trans hD), (div_lt_one (zero_lt_one.trans hD)).2 hD⟩

lemma policyAccuracy_mem {m : ℕ} (hm : 2≤m) {zlo : ℝ}
    (hz : zlo∈Ioo (0 : ℝ) (1/4)) : policyAccuracy m zlo ∈ Ioo (0 : ℝ) 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : 0 ≤ targetCountCutoff m := by unfold targetCountCutoff; positivity
  have hD : (2 : ℝ) ≤ (m : ℝ)*(1+targetCountCutoff m)^2 := by
    calc
      _ = 2*1 := by ring
      _ ≤ _ := mul_le_mul hmR (one_le_pow₀ (by linarith)) zero_le_one (by positivity)
  exact ⟨div_pos hz.1 (zero_lt_two.trans_le hD),
    (div_lt_one (zero_lt_two.trans_le hD)).2 (hz.2.trans_le (by linarith))⟩

lemma policyFailure_mem {n m J : ℕ} (hn : 0<n) (hm : 2≤m) :
    policyFailureBound n m J ∈ Ioo (0 : ℝ) 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hJ : (1 : ℝ) ≤ (J : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hD : (1 : ℝ) < (m : ℝ)^2*(n : ℝ)*((J : ℝ)+1) := by
    calc
      _ < 4*1*1 := by norm_num
      _ ≤ _ := mul_le_mul (mul_le_mul (by nlinarith) hnR zero_le_one (by positivity))
        hJ zero_le_one (by positivity)
  exact ⟨one_div_pos.mpr (zero_lt_one.trans hD), (div_lt_one (zero_lt_one.trans hD)).2 hD⟩

noncomputable def activeArithmeticLearner (mu : ℝ) (b : ℚ) (_hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1)
    (n m : ℕ) (hn : 0<n) (hm : 2≤m) : Learner n (2*m) :=
  letI : NeZero m := ⟨by omega⟩
  let zlo := (1-(b : ℝ))/(b : ℝ)
  let J := familyGridSize m zlo (1/4)
  let hT := 1/(m : ℝ)
  let pT := 1/((m : ℝ)^2*(4*(m : ℝ)+1))
  let hP := policyAccuracy m zlo
  let pP := policyFailureBound n m J
  let hpT := targetFailure_mem hm
  let hpP := policyFailure_mem (J := J) hn hm
  learnerCore (J := J) mu zlo (1/4)
    (calibrationPlannerSeedLaw n m hT pT hpT) (calibrationPlannerSeedLaw n m hP pP hpP)
    (calibrationTargetCall hT pT hpT) (calibrationPlannerCall hP pP hpP)
    (measurable_calibrationTargetCall hT pT hpT) (measurable_calibrationPlannerCall hP pP hpP)

noncomputable def arithmeticCalibratedLearner (mu : ℝ) (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1)
    (n m : ℕ) : Learner n (2*m) :=
  if h : 0<n ∧ 2≤m then activeArithmeticLearner mu b hb n m h.1 h.2 else degenerateLearner n m

lemma arithmeticCalibratedLearner_accepts_cap (mu : ℝ) (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1)
    (n m : ℕ) (d : Reservoir n (2*m) × (arithmeticCalibratedLearner mu b hb n m).Seed)
    (t : ℝ) (i : Fin n) (H : History n) :
    (arithmeticCalibratedLearner mu b hb n m).policy.decide d t i 1 H = true := by
  revert d
  by_cases h : 0<n ∧ 2≤m
  · rw [arithmeticCalibratedLearner, dif_pos h]
    rintro ⟨y,r⟩
    letI : NeZero m := ⟨by omega⟩
    dsimp only [activeArithmeticLearner] at r ⊢
    exact (learnerCore_decide _ _ _ _ _ _ _ _ _ y r t i 1 H).trans
      (samplePolicy_accepts_cap _ _ _ _ _ _ _ _ _)
  · rw [arithmeticCalibratedLearner, dif_neg h]
    intro d
    exact degenerateLearner_accepts_cap n m d.1 d.2 t i H

/-- Reward and reach bounds for the actual arithmetic construction
(`upbayes:theorem`). The constants are fixed before the number of identities
and the unknown laws. -/
theorem exists_arithmetic_calibrated_learner (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (K : ℝ), 0<K ∧
      ∀ (n m : ℕ), 1≤m → ∀ P : Instance n,
        (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
        P.positiveCount≤2*Real.log (m : ℝ) →
        let L := arithmeticCalibratedLearner mu b hb n m
        (∀ᵐ ω : (L.randomizedPolicy P).World ∂P.worldLaw (L.randomizedPolicy P).seedLaw,
          L.policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
        optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
        ∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨b,hb,K,hK,hMain⟩ := exists_calibrated_bounded_of_planner_confidence mu hmu hmuHi
  refine ⟨b,hb,max 1 K,hK.trans_le (le_max_right _ _),?_⟩
  intro n m hm P hcap hMean hM hL
  dsimp only
  let L := arithmeticCalibratedLearner mu b hb n m
  refine ⟨Filter.Eventually.of_forall (fun ω i _ hi => ?_),?_⟩
  · change (L.policy).decide ω.2.2 (ω.2.1 i) i (ω.1 i) _ = true
    rw [hi]
    exact arithmeticCalibratedLearner_accepts_cap mu b hb n m ω.2.2 _ _ _
  · by_cases h : 0<n ∧ 2≤m
    · letI : NeZero n := ⟨by omega⟩
      letI : NeZero m := ⟨by omega⟩
      let zlo := (1-(b : ℝ))/(b : ℝ)
      let J := familyGridSize m zlo (1/4)
      let hT := 1/(m : ℝ)
      let pT := 1/((m : ℝ)^2*(4*(m : ℝ)+1))
      let hP := policyAccuracy m zlo
      let pP := policyFailureBound n m J
      let hpT := targetFailure_mem h.2
      let hpP := policyFailure_mem (J := J) h.1 h.2
      have hStats := hMain n m P hcap hMean hM hL
        (CalibrationPlannerSeed n m hT pT hpT) (CalibrationPlannerSeed n m hP pP hpP)
        (calibrationPlannerSeedLaw n m hT pT hpT) (calibrationPlannerSeedLaw n m hP pP hpP)
        (calibrationTargetCall hT pT hpT) (calibrationPlannerCall hP pP hpP)
        (measurable_calibrationTargetCall hT pT hpT) (measurable_calibrationPlannerCall hP pP hpP)
        (calibrationTargetCall_correct_ae P hcap mu (targetAccuracy_mem h.2) hpT)
        (fun q hq hc A u z hu hz => calibrationPlannerCall_correct hP pP
          (policyAccuracy_mem h.2 (calibrationEndpoint_coefficient_bounds hb)) hpP q hq hc A u z hu hz)
      rw [arithmeticCalibratedLearner, dif_pos h]
      have hCompare := div_le_div_of_nonneg_right (le_max_right 1 K) (Nat.cast_nonneg m : (0 : ℝ)≤m)
      exact ⟨(sub_le_sub_left hCompare _).trans hStats.1,
        fun i => (sub_le_sub_left hCompare _).trans (hStats.2 i)⟩
    · by_cases hn : 0<n
      · have hOne : m=1 := by omega
        subst m
        have hUp := optimalCompetitiveRatio_le_one
        have hM0 := P.expectedMaximum_nonnegative
        have hC : optimalCompetitiveRatio*P.expectedMaximum ≤ max 1 K :=
          (mul_le_of_le_one_left hM0 hUp).trans (hM.trans (le_trans (by norm_num) (le_max_left _ _)))
        refine ⟨?_,fun i => ?_⟩
        · calc
            _ ≤ 0 := by simpa only [Nat.cast_one, div_one] using sub_nonpos.mpr hC
            _ ≤ _ := (L.randomizedPolicy P).expectedReward_nonnegative P
        · calc
            _ ≤ 0 := by simpa only [Nat.cast_one, div_one] using
              sub_nonpos.mpr (hUp.trans (le_max_left 1 K))
            _ ≤ _ := L.reachProbability_nonnegative P i
      · have hn0 : n=0 := by omega
        subst n
        have he : P.expectedMaximum=0 := by
          unfold Instance.expectedMaximum
          have h : (Instance.maximum : (Fin 0 → ℝ) → ℝ) = fun _ => 0 := by
            funext x
            exact le_antisymm (Instance.maximum_le x (le_refl (0 : ℝ)) (fun i => Fin.elim0 i))
              (Instance.maximum_nonnegative x)
          rw [h, integral_zero]
        exact False.elim ((not_le_of_gt hmu) (he ▸ hMean))

/-- The (3m+q_m) reduction applied to the arithmetic calibrated construction. -/
theorem arithmetic_outer_sample_upper_bound :
    ∃ (C : ℝ), 0<C ∧ ∀ k : ℕ, 1≤k → FeasibleBudget (C/(k : ℝ)) k := by
  have hmu : (0 : ℝ)<1/10000000 := by norm_num
  have hmuHi : (1/10000000 : ℝ)<1/80 := by norm_num
  obtain ⟨b,hb,K,hK,hBound⟩ := exists_arithmetic_calibrated_learner _ hmu hmuHi
  refine ⟨outerUpperConstant K, outer_sample_upper_bound_of_bounded_guarantees hK.le
    (arithmeticCalibratedLearner (1/10000000) b hb) ?_⟩
  intro n m hm Q hMean hCount _ hcap
  exact hBound n m hm Q hcap hMean.1 hMean.2 hCount

end ProphetSecretary.Statistics.Calibration
