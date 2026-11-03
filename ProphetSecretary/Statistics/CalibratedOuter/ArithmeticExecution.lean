import ProphetSecretary.Statistics.CalibratedOuter.PreparedExecution
import ProphetSecretary.Statistics.ArithmeticCalibratedLearner

/-!
# The outer learner with its actual causal sampling loop

The samples are read by the fixed computed request scan. Statistical
analysis may use the equivalent product of the three blocks because the
scan reads the full blocks on every raw training outcome.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis

noncomputable def arithmeticOuterLearner (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1)
    (n m : ℕ) (hm : 1≤m) : Learner n (outerSampleBudget m) :=
  computedOuterLearner m hm (arithmeticCalibratedLearner (1/10000000) b hb n m)

theorem exists_arithmetic_outer_learner :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (K : ℝ), 0<K ∧
      ∀ (n m : ℕ) (hm : outerRequiredScale K≤m),
        (arithmeticOuterLearner b hb n m (by unfold outerRequiredScale at hm; omega)).Guarantees
          (optimalCompetitiveRatio-(outerReductionLocalConstant K+3*optimalCompetitiveRatio)/(m : ℝ)) := by
  have hmu : (0 : ℝ)<1/10000000 := by norm_num
  have hmuHi : (1/10000000 : ℝ)<1/80 := by norm_num
  obtain ⟨b,hb,K,hK,hBound⟩ := exists_arithmetic_calibrated_learner _ hmu hmuHi
  refine ⟨b,hb,K,hK,?_⟩
  intro n m hm P hP
  let L := arithmeticCalibratedLearner (1/10000000) b hb n m
  have hmBig : 2000000000≤m := by unfold outerRequiredScale at hm; omega
  have hm1 : 1≤m := by omega
  have hm0 : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hKm : 2*K≤(m : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈2*K⌉₊≤m by unfold outerRequiredScale at hm; omega))
  have hρ : 0≤optimalCompetitiveRatio-K/(m : ℝ) := by
    have h := (div_le_iff₀ hm0).mpr (by linarith only [hKm] : K≤(1/2)*(m : ℝ))
    linarith only [h,half_le_optimalCompetitiveRatio]
  change _ ≤ (computedOuterLearner m hm1 L).expectedReward P
  rw [computedOuterLearner_reward]
  exact outer_reduction_of_bounded_guarantees m (by omega) L hK.le
    optimalCompetitiveRatio_nonnegative (by linarith only [optimalCompetitiveRatio_le_threeQuarters]) hρ
    (fun Q hMean hL _ hcap => hBound n m hm1 Q hcap hMean.1 hMean.2 hL) P hP.1

end ProphetSecretary.Statistics.Calibration
