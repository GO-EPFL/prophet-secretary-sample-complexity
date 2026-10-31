import ProphetSecretary.Limiting.WeightedOrdering

/-!
# Uniform rarity after continuous-weight ordering

A strictly positive lower bound for the ordering weight on a band converts
the reciprocal-rank score estimate into the required maximum tail bound.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal BigOperators Classical
namespace ProphetSecretary.Limiting

lemma tail_mass_mul_le_integral_weight (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) {b c : ℝ} (hband : ∀ x, b < x → c ≤ w x) :
    c * (p : Measure ℝ).real (Ioi b) ≤ ∫ x, w x ∂(p : Measure ℝ) := by
  have hmono : (∫ x, (Ioi b).indicator (fun _ : ℝ => c) x ∂(p : Measure ℝ)) ≤ ∫ x, w x ∂(p : Measure ℝ) := by
    apply integral_mono ((integrable_const c).indicator measurableSet_Ioi) (w.integrable _)
    intro x
    by_cases hx : x ∈ Ioi b
    · rw [Set.indicator_of_mem hx]
      exact hband x hx
    · rw [Set.indicator_of_notMem hx]
      exact hw x
  simpa only [integral_indicator_const c measurableSet_Ioi,smul_eq_mul,mul_comm] using hmono

theorem weightOrderedPaddedLaw_tail_le {n : ℕ} (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0)
    (hWeight : (∑ i, ∫ x, w x ∂P.law i) ≤ 1)
    {b c : ℝ} (hc : 0 < c) (hband : ∀ x, b < x → c ≤ w x) (j : ℕ) :
    (weightOrderedPaddedLaw P w j : Measure ℝ).real (Ioi b) ≤ 1 / (c * (j+1 : ℕ)) := by
  have hm := tail_mass_mul_le_integral_weight (weightOrderedPaddedLaw P w j) w hw hband
  have hs := (weightOrderedScore_le_total_div_rank P w hw hw0 j).trans
    (div_le_div_of_nonneg_right hWeight (Nat.cast_nonneg _))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < c * (j+1 : ℕ))).mpr
  have h := mul_le_mul_of_nonneg_right (hm.trans hs) (by positivity : (0 : ℝ) ≤ (j+1 : ℕ))
  rw [div_mul_cancel₀ _ (by positivity : ((j+1 : ℕ) : ℝ) ≠ 0)] at h
  nlinarith

/-- The cutoff and rank are chosen before every instance and residual index. -/
theorem weightOrdered_residual_uniformly_rare (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0)
    (hWeight : ∀ m, (∑ i, ∫ x, w x ∂(P m).law i) ≤ 1)
    {b c : ℝ} (hc : 0 < c) (hband : ∀ x, b < x → c ≤ w x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m j, N ≤ j → (weightOrderedPaddedLaw (P m) w j : Measure ℝ).real (Ioi b) < ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1 / (c*ε))
  refine ⟨N,?_⟩
  intro m j hNj
  have hNjR : (N : ℝ) ≤ j := by exact_mod_cast hNj
  have hj : 1 / (c*ε) < (j+1 : ℕ) := by push_cast; linarith
  have hden : 1 < c * ε * (j+1 : ℕ) := by
    simpa only [mul_comm] using (div_lt_iff₀ (mul_pos hc hε)).mp hj
  have hfrac : 1 / (c * (j+1 : ℕ)) < ε := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < c * (j+1 : ℕ))).mpr
    nlinarith
  exact (weightOrderedPaddedLaw_tail_le (P m) w hw hw0 (hWeight m) hc hband j).trans_lt hfrac

end ProphetSecretary.Limiting
