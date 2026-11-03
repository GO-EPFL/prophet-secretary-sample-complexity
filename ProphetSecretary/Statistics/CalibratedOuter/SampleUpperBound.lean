import ProphetSecretary.Statistics.CalibratedOuter.Reduction
import ProphetSecretary.Statistics.CalibratedOuter.SamplingBudget
import ProphetSecretary.Model.BudgetPadding
import ProphetSecretary.Model.HalfGuarantee
import ProphetSecretary.Model.TwoOfferCompetitiveBound

/-!
# Conditional sample upper bound for every integer budget

The bounded family and its uniform constant are fixed before all unknown laws.
The explicit outer constant covers the large-budget choice m=floor(k/10) and
the rejecting policy for the remaining budgets. All sampling budgets hold on
every raw outcome. This is the reduction of `upouter:theorem` conditional on
the bounded-family guarantees from `upbayes:theorem`.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis

noncomputable def outerRequiredScale (K : ℝ) : ℕ := 2000000000+⌈2*K⌉₊

noncomputable def outerUpperConstant (K : ℝ) : ℝ :=
  20*(outerReductionLocalConstant K+3*optimalCompetitiveRatio)+20*(outerRequiredScale K:ℝ)

lemma outerUpperConstant_positive {K : ℝ} (hK : 0≤K) : 0<outerUpperConstant K := by
  have hD := outerReductionLocalConstant_nonneg hK
  have hC := optimalCompetitiveRatio_nonnegative
  have hN : (0:ℝ)<outerRequiredScale K := by exact_mod_cast (show 0<outerRequiredScale K by unfold outerRequiredScale;omega)
  unfold outerUpperConstant
  positivity

noncomputable def outerBudgetLearner (K : ℝ) (bounded : (n m : ℕ) → Learner n (2*m)) (k n : ℕ) : Learner n k :=
  if hk : 10*outerRequiredScale K≤k then
    (outerLearner (k/10) (by unfold outerRequiredScale at hk;omega) (bounded n (k/10))).padBudget
      (outerSampleBudget_div_ten_le k (by unfold outerRequiredScale at hk;omega))
  else Learner.rejecting n k

lemma outerBudgetLearner_expectedReward_large (K : ℝ) (bounded : (n m : ℕ) → Learner n (2*m))
    (k n : ℕ) (hk : 10*outerRequiredScale K≤k) (P : Instance n) :
    (outerBudgetLearner K bounded k n).expectedReward P=
      (outerLearner (k/10) (by unfold outerRequiredScale at hk;omega) (bounded n (k/10))).expectedReward P := by
  rw [outerBudgetLearner,dif_pos hk,Learner.padBudget_expectedReward]

/-- The actual outer family guarantees the claimed ratio under the bounded
family's uniform reward/reach/cap hypotheses. No bounded hypothesis is discharged
by the definition of the family itself. -/
theorem outerBudgetLearner_guarantees_of_bounded_guarantees
    {K : ℝ} (hK : 0≤K) (bounded : (n m : ℕ) → Learner n (2*m))
    (hBounded : ∀ (n m : ℕ), 1≤m → ∀ Q : Instance n,
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m:ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      (∀ᵐ ω : ((bounded n m).randomizedPolicy Q).World ∂Q.worldLaw ((bounded n m).randomizedPolicy Q).seedLaw,
        (bounded n m).policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (optimalCompetitiveRatio*Q.expectedMaximum-K/(m:ℝ)≤(bounded n m).expectedReward Q) ∧
      (∀ i, optimalCompetitiveRatio-K/(m:ℝ)≤(bounded n m).reachProbability Q i))
    (k n : ℕ) (hk1 : 1≤k) :
    (outerBudgetLearner K bounded k n).Guarantees (optimalCompetitiveRatio-outerUpperConstant K/(k:ℝ)) := by
  intro P hP
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hA : 0≤outerReductionLocalConstant K+3*optimalCompetitiveRatio :=
    add_nonneg (outerReductionLocalConstant_nonneg hK) (mul_nonneg (by norm_num) optimalCompetitiveRatio_nonnegative)
  by_cases hk : 10*outerRequiredScale K≤k
  · have hmN : outerRequiredScale K≤k/10 := by omega
    have hmLarge : 2000000000≤k/10 := by unfold outerRequiredScale at hmN;omega
    have hmMain : 2000000≤k/10 := by omega
    have hm1 : 1≤k/10 := by omega
    have hmR : (0:ℝ)<((k/10:ℕ):ℝ) := by exact_mod_cast (show 0<k/10 by omega)
    have hCeil : (⌈2*K⌉₊:ℝ)≤((k/10:ℕ):ℝ) := by
      exact_mod_cast (show ⌈2*K⌉₊≤k/10 by unfold outerRequiredScale at hmN;omega)
    have hKm : 2*K≤((k/10:ℕ):ℝ) := (Nat.le_ceil _).trans hCeil
    have hDiv : K/((k/10:ℕ):ℝ)≤(1:ℝ)/2 := (div_le_iff₀ hmR).mpr (by linarith only [hKm])
    have hρ : 0≤optimalCompetitiveRatio-K/((k/10:ℕ):ℝ) := by linarith only [hDiv,half_le_optimalCompetitiveRatio]
    have hReduction := outer_reduction_of_bounded_guarantees (k/10) hmMain (bounded n (k/10)) hK
      optimalCompetitiveRatio_nonnegative (by linarith only [optimalCompetitiveRatio_le_threeQuarters]) hρ
      (hBounded n (k/10) hm1) P hP.1
    have hRate0 := outer_deficit_div_ten_le (show 20≤k by omega) hA
    have hConst : 20*(outerReductionLocalConstant K+3*optimalCompetitiveRatio)≤outerUpperConstant K := by
      unfold outerUpperConstant
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Nat.cast_nonneg (outerRequiredScale K)))
    have hRate : (outerReductionLocalConstant K+3*optimalCompetitiveRatio)/((k/10:ℕ):ℝ)≤outerUpperConstant K/(k:ℝ) :=
      hRate0.trans (div_le_div_of_nonneg_right hConst hkR.le)
    rw [outerBudgetLearner_expectedReward_large K bounded k n hk P]
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hRate optimalCompetitiveRatio) hP.2.le).trans hReduction
  · have hkSmall : (k:ℝ)≤10*(outerRequiredScale K:ℝ) := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hk))
    have hConst : (k:ℝ)≤outerUpperConstant K := by
      unfold outerUpperConstant
      nlinarith only [hkSmall,hA,(show (0:ℝ)≤(outerRequiredScale K:ℝ) from Nat.cast_nonneg _)]
    have hRatio : 1≤outerUpperConstant K/(k:ℝ) := (le_div_iff₀ hkR).mpr (by simpa only [one_mul] using hConst)
    have hCoeff : optimalCompetitiveRatio-outerUpperConstant K/(k:ℝ)≤0 := by
      linarith only [hRatio,optimalCompetitiveRatio_le_one]
    rw [outerBudgetLearner,dif_neg hk]
    exact (mul_nonpos_of_nonpos_of_nonneg hCoeff P.expectedMaximum_nonnegative).trans
      (((Learner.rejecting n k).randomizedPolicy P).expectedReward_nonnegative P)

/-- Conditional form of the universal sample upper bound, with an explicit
constant and a learner family independent of all online laws. -/
theorem outer_sample_upper_bound_of_bounded_guarantees
    {K : ℝ} (hK : 0≤K) (bounded : (n m : ℕ) → Learner n (2*m))
    (hBounded : ∀ (n m : ℕ), 1≤m → ∀ Q : Instance n,
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m:ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      (∀ᵐ ω : ((bounded n m).randomizedPolicy Q).World ∂Q.worldLaw ((bounded n m).randomizedPolicy Q).seedLaw,
        (bounded n m).policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (optimalCompetitiveRatio*Q.expectedMaximum-K/(m:ℝ)≤(bounded n m).expectedReward Q) ∧
      (∀ i, optimalCompetitiveRatio-K/(m:ℝ)≤(bounded n m).reachProbability Q i)) :
    0<outerUpperConstant K ∧ ∀ k : ℕ, 1≤k → FeasibleBudget (outerUpperConstant K/(k:ℝ)) k := by
  refine ⟨outerUpperConstant_positive hK,?_⟩
  intro k hk
  exact ⟨outerBudgetLearner K bounded k,fun n => outerBudgetLearner_guarantees_of_bounded_guarantees hK bounded hBounded k n hk⟩

end ProphetSecretary.Statistics.Calibration
