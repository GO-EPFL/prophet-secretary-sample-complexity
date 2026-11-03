import ProphetSecretary.Statistics.CalibratedOuter.FairRankExecution
import ProphetSecretary.Statistics.CalibrationClockScale

/-!
# The outer reduction with fair marks

The analytic reduction uses continuous marks. The independent grid-mark
coupling adds a benchmark-relative loss, which fits the same (1/m) rate.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis

lemma outerMarkGrid_bound (n m : ℕ) :
    m^2*(n*(outerSampleBudget m+1))^2≤2^outerMarkBits n m := by
  rw [outerSampleBudget_eq]
  exact Nat.le_pow_clog (by decide) _

theorem fair_outer_reduction_of_bounded_guarantees {n m : ℕ} (hn : 0<n) (hm : 2000000≤m)
    (L : Learner n (2*m)) {C K : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hCupper : C≤997/1000) (hρ : 0≤C-K/(m : ℝ))
    (hBounded : ∀ Q : Instance n,
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m : ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      (∀ᵐ ω : (L.randomizedPolicy Q).World ∂Q.worldLaw (L.randomizedPolicy Q).seedLaw,
        L.policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (C*Q.expectedMaximum-K/(m : ℝ)≤L.expectedReward Q) ∧
      (∀ i, C-K/(m : ℝ)≤L.reachProbability Q i))
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (C-(outerReductionLocalConstant K+3*C+1)/(m : ℝ))*P.expectedMaximum≤
      (outerFairMarkLearner (by omega : 1≤m) L (outerMarkBits n m)).expectedReward P := by
  let hm1 : 1≤m := by omega
  have ha := outer_reduction_of_bounded_guarantees m hm L hK hC hCupper hρ hBounded P hP
  have hb := outerFairMarkLearner_reward_loss hn hm1 L (outerMarkBits n m) (outerMarkGrid_bound n m) P hP
  have hmR : (1 : ℝ)≤m := by exact_mod_cast hm1
  have hp : (0 : ℝ)<m := by linarith only [hmR]
  have hExtra : P.expectedMaximum/(2*(m : ℝ)^2)≤P.expectedMaximum/(m : ℝ) :=
    div_le_div_of_nonneg_left P.expectedMaximum_nonnegative hp (by nlinarith only [hmR,sq_nonneg ((m : ℝ)-1)])
  have hScale : (C-(outerReductionLocalConstant K+3*C+1)/(m : ℝ))*P.expectedMaximum =
      (C-(outerReductionLocalConstant K+3*C)/(m : ℝ))*P.expectedMaximum-P.expectedMaximum/(m : ℝ) := by
    ring
  rw [hScale]
  calc
    _ ≤ (outerLearner m hm1 L).expectedReward P-P.expectedMaximum/(2*(m : ℝ)^2) :=
      sub_le_sub ha hExtra
    _ ≤ _ := by linarith only [hb]

/-- The finite mark correction preserves the linear sample rate when the
bounded rank learner is supplied. -/
theorem fair_rank_outer_at_accuracy_of_bounded {K : ℝ} (hK : 0≤K)
    (bounded : (n m : ℕ) → 0<n → 2≤m → RankLearner n (2*m))
    (hBounded : ∀ (n m : ℕ) (hn : 0<n) (hm : 2≤m) (Q : Instance n),
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m : ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      let L := (bounded n m hn hm).rankToClock
      (∀ᵐ ω : (L.randomizedPolicy Q).World ∂Q.worldLaw (L.randomizedPolicy Q).seedLaw,
        L.policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (optimalCompetitiveRatio*Q.expectedMaximum-K/(m : ℝ)≤L.expectedReward Q) ∧
      (∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability Q i)) :
    ∃ A eps0 : ℝ, 0<A ∧ 0<eps0 ∧ ∀ eps∈Ioo (0 : ℝ) eps0,
      ∃ (m : ℕ) (hm : 2≤m), (outerSampleBudget m : ℝ)≤A/eps ∧
        ∀ (n : ℕ) (hn : 0<n), (outerFairRankLearner (by omega : 1≤m)
          (bounded n m hn hm) (outerMarkBits n m)).Guarantees (optimalCompetitiveRatio-eps) := by
  let C := optimalCompetitiveRatio
  let D := outerReductionLocalConstant K+3*C+1
  let S := outerRequiredScale K
  have hD : 0<D := by
    have h₁ := outerReductionLocalConstant_nonneg hK
    have h₂ := optimalCompetitiveRatio_nonnegative
    dsimp [D,C]
    linarith
  have hS : 0<S := by dsimp [S,outerRequiredScale]; omega
  have hSR : (0 : ℝ)<S := by exact_mod_cast hS
  refine ⟨4*(D+1),min 1 (D/(S : ℝ)),by positivity,lt_min zero_lt_one (div_pos hD hSR),?_⟩
  intro eps he
  have he0 := he.1
  have he1 : eps<1 := he.2.trans_le (min_le_left _ _)
  let m := ⌈D/eps⌉₊
  have hmD : D/eps≤(m : ℝ) := Nat.le_ceil _
  have hmS : S≤m := by
    have heS : eps<D/(S : ℝ) := he.2.trans_le (min_le_right _ _)
    have h := ((lt_div_iff₀ he0).mpr (by
      simpa only [mul_comm] using (lt_div_iff₀ hSR).mp heS)).le.trans hmD
    exact_mod_cast h
  have hmBig : 2000000000≤m := by dsimp [S,outerRequiredScale] at hmS; omega
  have hm2 : 2≤m := by omega
  have hm0 : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hCeil : (m : ℝ)≤D/eps+1 := (Nat.ceil_lt_add_one (div_nonneg hD.le he0.le)).le
  have hBudget := outerSampleBudget_le_four_mul m hmBig
  refine ⟨m,hm2,?_,?_⟩
  · calc
      (outerSampleBudget m : ℝ) ≤ 4*(m : ℝ) := by exact_mod_cast hBudget
      _ ≤ 4*(D/eps+1) := mul_le_mul_of_nonneg_left hCeil (by norm_num)
      _ ≤ _ := by
        apply (le_div_iff₀ he0).mpr
        have h : 4*(D/eps+1)*eps=4*(D+eps) := by field_simp
        rw [h]
        linarith only [he1]
  · intro n hn P hP
    let R := bounded n m hn hm2
    have hKm : 2*K≤(m : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈2*K⌉₊≤m by dsimp [S,outerRequiredScale] at hmS; omega))
    have hρ : 0≤C-K/(m : ℝ) := by
      have hHalf := half_le_optimalCompetitiveRatio
      have hk : K/(m : ℝ)≤1/2 := (div_le_iff₀ hm0).mpr (by linarith only [hKm])
      dsimp [C]
      linarith only [hHalf,hk]
    have hReward := fair_outer_reduction_of_bounded_guarantees hn (by omega) R.rankToClock
      hK optimalCompetitiveRatio_nonnegative (by linarith only [optimalCompetitiveRatio_le_threeQuarters])
      hρ (hBounded n m hn hm2) P hP.1
    rw [outerFairRankLearner_expectedReward]
    have hErr : D/(m : ℝ)≤eps := (div_le_iff₀ hm0).mpr (by
      simpa only [mul_comm] using (div_le_iff₀ he0).mp hmD)
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hErr C)
      P.expectedMaximum_nonnegative).trans hReward

end ProphetSecretary.Statistics.Calibration
