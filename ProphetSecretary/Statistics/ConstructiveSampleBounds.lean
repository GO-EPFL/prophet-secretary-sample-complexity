import ProphetSecretary.Statistics.ArithmeticCalibratedLearner
import ProphetSecretary.Model.SampleComplexityMinimum
import ProphetSecretary.LowerBound.SampleLowerBound

/-!
# Sample budgets of the constructive upper bound

The actual arithmetic calibrated learner supplies the feasible budgets.
The lower bound still ranges over all admissible adaptive learners.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Statistics.Calibration

/-- The two-sided sample estimates of `thm:theta-main`, using the calibrated
arithmetic learner for the upper estimate. -/
theorem constructive_sample_complexity_bounds :
    ∃ a A eps0 : ℝ, 0<a ∧ a≤A ∧ 0<eps0 ∧ ∀ eps∈Ioo (0 : ℝ) eps0,
      sampleComplexity eps<⊤ ∧ a/eps≤((sampleComplexity eps).toNat : ℝ) ∧
      ((sampleComplexity eps).toNat : ℝ)≤A/eps := by
  obtain ⟨a,η,ha,hη,hLow⟩ := LowerBound.sample_lower_bound
  obtain ⟨K,hK,hUpper⟩ := arithmetic_outer_sample_upper_bound
  refine ⟨a,max a (K+1),min η 1,ha,le_max_left _ _,lt_min hη zero_lt_one,?_⟩
  intro eps he
  let k := ⌈K/eps⌉₊
  have hε := he.1
  have hk : 0<k := Nat.ceil_pos.mpr (div_pos hK hε)
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hKk : K/eps≤(k : ℝ) := Nat.le_ceil _
  have hErr : K/(k : ℝ)≤eps := (div_le_iff₀ hkR).mpr (by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hKk)
  have hFeasible : FeasibleBudget eps k := by
    obtain ⟨L,hL⟩ := hUpper k (by omega)
    refine ⟨L,?_⟩
    intro n P hP
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hErr optimalCompetitiveRatio)
      P.expectedMaximum_nonnegative).trans (hL n P hP)
  have hNE : ∃ k : ℕ, FeasibleBudget eps k := ⟨k,hFeasible⟩
  have hMinimum := sampleComplexity_toNat_feasible hNE
  have hCeil : (k : ℝ)≤K/eps+1 := (Nat.ceil_lt_add_one (div_nonneg hK.le hε.le)).le
  have hSmall : eps≤1 := he.2.le.trans (min_le_right _ _)
  have hBudget : (k : ℝ)≤(K+1)/eps := by
    apply (le_div_iff₀ hε).mpr
    have h := mul_le_mul_of_nonneg_right hCeil hε.le
    rw [add_mul,div_mul_cancel₀ _ hε.ne',one_mul] at h
    exact h.trans (add_le_add le_rfl hSmall)
  refine ⟨lt_top_iff_ne_top.mpr (sampleComplexity_ne_top hNE),
    hLow eps ⟨hε,he.2.trans_le (min_le_left _ _)⟩ _ hMinimum,?_⟩
  calc
    _ ≤ (k : ℝ) := by exact_mod_cast sampleComplexity_toNat_le hFeasible
    _ ≤ (K+1)/eps := hBudget
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_right a (K+1)) hε.le

end ProphetSecretary.Statistics
