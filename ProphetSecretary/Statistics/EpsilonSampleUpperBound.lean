import ProphetSecretary.Statistics.SampleUpperBound
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Explicit epsilon budgets from the universal upper theorem

The learner family and hard budget are unchanged when the permitted error
increases. Choosing ceil(Kout/epsilon) gives the paper's upper sample bound,
with constant Kout+1 fixed before epsilon and the unknown instance.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model

lemma feasibleBudget_mono_error {eps eps' : ℝ} {k : ℕ}
    (h : FeasibleBudget eps k) (hle : eps≤eps') : FeasibleBudget eps' k := by
  obtain ⟨learners,hGuarantee⟩ := h
  refine ⟨learners,?_⟩
  intro n P hP
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hle optimalCompetitiveRatio)
    P.expectedMaximum_nonnegative).trans (hGuarantee n P hP)

end ProphetSecretary.Model
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

theorem epsilon_sample_upper_bound :
    ∃ Kout : ℝ, 0<Kout ∧ ∀ eps : ℝ, 0<eps →
      FeasibleBudget eps (Nat.ceil (Kout/eps)) ∧
      sampleComplexity eps≤(Nat.ceil (Kout/eps) : ℕ∞) ∧
      (eps<1 → (Nat.ceil (Kout/eps) : ℝ)≤(Kout+1)/eps) := by
  obtain ⟨Kout,hKout,hUpper⟩ := sample_upper_bound
  refine ⟨Kout,hKout,?_⟩
  intro eps hEps
  let k := Nat.ceil (Kout/eps)
  have hRatio : 0<Kout/eps := div_pos hKout hEps
  have hk : 0<k := Nat.ceil_pos.mpr hRatio
  have hKReal : (0 : ℝ)<k := Nat.cast_pos.mpr hk
  have hCount : Kout/eps≤(k : ℝ) := Nat.le_ceil _
  have hError : Kout/(k : ℝ)≤eps := by
    apply (div_le_iff₀ hKReal).mpr
    have h := (div_le_iff₀ hEps).mp hCount
    simpa only [mul_comm] using h
  have hFeasible : FeasibleBudget eps k := feasibleBudget_mono_error (hUpper k hk) hError
  refine ⟨hFeasible,?_,?_⟩
  · exact sInf_le ⟨k,hFeasible,rfl⟩
  · intro hEpsOne
    apply (le_div_iff₀ hEps).mpr
    have hCeil : (k : ℝ)≤Kout/eps+1 := (Nat.ceil_lt_add_one hRatio.le).le
    have hMul := mul_le_mul_of_nonneg_right hCeil hEps.le
    rw [add_mul,div_mul_cancel₀ _ hEps.ne',one_mul] at hMul
    exact hMul.trans (add_le_add le_rfl hEpsOne.le)

end ProphetSecretary.Statistics
