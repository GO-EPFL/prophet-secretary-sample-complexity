import ProphetSecretary.Statistics.CalibratedOuter.BinaryGuarantees

/-!
# Finite-bit learning from an encoded accuracy

The accuracy front end computes the sample scale once. A fixed integer
dominates both the minimum scale for the outer reduction and its reward
deficit constant.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model

private lemma height_at_integer_bound (q : ℚ) :
    RationalHeight q (max q.num.natAbs q.den) := by
  have h := (Nat.lt_two_pow_self (n := max q.num.natAbs q.den)).le
  exact ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩

/-- The counted front end chooses the very scale used in the reward and
hard-budget guarantees. Its bit cost is added once to the work of the
public-scale tape program. -/
theorem binary_finite_bit_learner_from_accuracy :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (D H C e : ℕ),
      0<D ∧ RationalHeight (1/10000000 : ℚ) H ∧
      RationalHeight ((1-b)/b) H ∧ 2≤H ∧
      (∀ x : BinaryScheduleInput ((1-b)/b) zInv, x.HasHardBounds H C e) ∧
      ∀ (eps : BinaryRational), (eps.value : ℝ)∈Ioo (0 : ℝ) 1 →
        let q := countedBinaryAccuracyScale D eps
        ∃ hm : 2≤q.1, (outerSampleBudget q.1 : ℝ)≤4*((D : ℝ)+1)/(eps.value : ℝ) ∧
          (∀ B, RationalHeight eps.value B → q.2≤binaryAccuracyScaleWork D B) ∧
          ∀ (n : ℕ) (hn : 0<n) (P : RationalOfferInstance n), P.toInstance.HasPositiveFiniteMaximum →
            let a : FairCalibrationParameters n q.1 :=
              ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
            let z := BinaryRational.ofRat ((1-b)/b)
            let hz : (z.value : ℝ)=a.zlo := by
              simp only [z,BinaryRational.ofRat_value,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
              rfl
            (optimalCompetitiveRatio-(eps.value : ℝ))*P.toInstance.expectedMaximum ≤
              a.binaryTapeExpectedReward (BinaryRational.ofRat (1/10000000)) z hz P := by
  have hμ : (0 : ℝ)<1/10000000 := by norm_num
  have hμ' : (1/10000000 : ℝ)<1/80 := by norm_num
  obtain ⟨b,hb,zInv,hInv,K,hK,hStat⟩ := exists_finite_rank_calibrated_learner _ hμ hμ'
  let deficit := outerReductionLocalConstant K+3*optimalCompetitiveRatio+1
  let D := outerRequiredScale K+⌈deficit⌉₊+1
  let q₁ : ℚ := 1/10000000
  let q₂ : ℚ := (1-b)/b
  let H := max 2 (max (max q₁.num.natAbs q₁.den) (max q₂.num.natAbs q₂.den))
  obtain ⟨C,e,hWork⟩ := BinaryScheduleInput.measuredProgramWork_polynomial (zlo := q₂) (zInv := zInv) H
  refine ⟨b,hb,zInv,hInv,D,H,C,e,by dsimp [D]; omega,
    (height_at_integer_bound q₁).mono ((le_max_left _ _).trans (le_max_right _ _)),
    (height_at_integer_bound q₂).mono ((le_max_right _ _).trans (le_max_right _ _)),
    le_max_left _ _,hWork,?_⟩
  intro eps hE
  dsimp only
  let s := (eps.value : ℝ)
  let m := (countedBinaryAccuracyScale D eps).1
  have hmEq : m=⌈(D : ℝ)/s⌉₊ := countedBinaryAccuracyScale_value D eps
  have hmD : (D : ℝ)/s≤(m : ℝ) := by rw [hmEq]; exact Nat.le_ceil _
  have hs0 : 0<s := hE.1
  have hs1 : s<1 := hE.2
  have hD : outerRequiredScale K≤D := by dsimp [D]; omega
  have hScale : outerRequiredScale K≤m := by
    have h : (D : ℝ)≤(D : ℝ)/s :=
      (le_div_iff₀ hE.1).mpr (mul_le_of_le_one_right (Nat.cast_nonneg _) hE.2.le)
    exact hD.trans (by exact_mod_cast h.trans hmD)
  have hmBig : 2000000000≤m := by dsimp [outerRequiredScale] at hScale; omega
  have hm : 2≤m := by omega
  have hmPos : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hCeil : (m : ℝ)≤(D : ℝ)/s+1 := by
    rw [hmEq]
    exact (Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) hE.1.le)).le
  refine ⟨hm,?_,(fun B h => countedBinaryAccuracyScale_work D B eps h),?_⟩
  · calc
      (outerSampleBudget m : ℝ) ≤ 4*(m : ℝ) := by exact_mod_cast outerSampleBudget_le_four_mul m hmBig
      _ ≤ 4*((D : ℝ)/s+1) := mul_le_mul_of_nonneg_left hCeil (by norm_num)
      _ ≤ 4*((D : ℝ)+1)/s := by
        apply (le_div_iff₀ hE.1).mpr
        have h : 4*((D : ℝ)/s+1)*s=4*((D : ℝ)+s) := by field_simp [hs0.ne']
        rw [h]
        linarith only [hs1]
  · intro n hn P hP
    let a : FairCalibrationParameters n m :=
      ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
    let L := a.finiteLearner (1/10000000)
    have hKm : 2*K≤(m : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈2*K⌉₊≤m by dsimp [outerRequiredScale] at hScale; omega))
    have hρ : 0≤optimalCompetitiveRatio-K/(m : ℝ) := by
      have hk : K/(m : ℝ)≤1/2 := (div_le_iff₀ hmPos).mpr (by linarith only [hKm])
      linarith only [half_le_optimalCompetitiveRatio,hk]
    have hReward := fair_outer_reduction_of_bounded_guarantees hn (by omega) L.rankToClock
      hK.le optimalCompetitiveRatio_nonnegative (by linarith only [optimalCompetitiveRatio_le_threeQuarters])
      hρ (fun Q hMean hCount _ hCap => by
        have hB := hStat n m hn hm Q hCap hMean.1 hMean.2 hCount
        refine ⟨Filter.Eventually.of_forall (fun ω i _ hx => ?_),?_,?_⟩
        · change L.rankToClock.policy.decide ω.2.2 (ω.2.1 i) i (ω.1 i) _=true
          rw [hx]
          exact a.finiteLearner_accepts_cap (1/10000000) ω.2.2.1 ω.2.2.2 _ i _
        · rw [RankLearner.rankToClock_expectedReward]
          exact hB.1
        · intro i
          rw [RankLearner.rankToClock_reachProbability]
          exact hB.2 i) P.toInstance hP.1
    have hD' : deficit≤(D : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈deficit⌉₊≤D by dsimp [D]; omega))
    have hErr : deficit/(m : ℝ)≤s := (div_le_iff₀ hmPos).mpr
      (hD'.trans (by simpa only [mul_comm] using (div_le_iff₀ hE.1).mp hmD))
    rw [FairCalibrationParameters.binaryTapeExpectedReward_eq,
      FairCalibrationParameters.binaryExpectedReward_eq_native,
      FairCalibrationParameters.nativeExpectedReward_eq,
      show ((BinaryRational.ofRat (1/10000000)).value : ℝ)=1/10000000 by
        rw [BinaryRational.ofRat_value]; norm_num,
      outerFairRankLearner_expectedReward]
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hErr _)
      P.toInstance.expectedMaximum_nonnegative).trans hReward

end ProphetSecretary.Statistics.Calibration
