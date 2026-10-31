import ProphetSecretary.Model.ScalarValueProperties

/-!
# Moving scalar weights along a bounded finite-instance sequence

The fixed-weight value limit and the uniform coefficient H+1 imply the
same value limit along convergent normalized weights. The number of offers
may vary arbitrarily; no policy convergence is inferred from this step.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace ProphetSecretary.Model

theorem optimalScalarValue_tendsto_along_weights (sizes : ℕ → ℕ)
    (P : ∀ m, Instance (sizes m)) {H a v : ℝ} (hH : 0≤H)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H) (lam : ℕ → ℝ)
    (hLam : ∀ m, lam m∈Icc (0 : ℝ) 1) (ha : a∈Icc (0 : ℝ) 1)
    (hWeight : Tendsto lam atTop (𝓝 a))
    (hFixed : Tendsto (fun m => optimalScalarValue (P m) a (1-a)) atTop (𝓝 v)) :
    Tendsto (fun m => optimalScalarValue (P m) (lam m) (1-lam m)) atTop (𝓝 v) := by
  have hError : Tendsto (fun m => (H+1)*|lam m-a|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero,mul_zero] using (hWeight.sub_const a).abs.const_mul (H+1)
  have hFixedError : Tendsto (fun m => |optimalScalarValue (P m) a (1-a)-v|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero] using (hFixed.sub_const v).abs
  have hUpper := hError.add hFixedError
  rw [zero_add] at hUpper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hUpper
  intro m
  have hP := (P m).integrable_maximum_of_bounded (hcap m)
  have hM := (P m).expectedMaximum_le_of_bounded hH (hcap m)
  have hLip := optimalScalarValue_weight_lipschitz (P m) hP (hLam m) ha
  have hBound := hLip.trans (mul_le_mul_of_nonneg_right (add_le_add hM le_rfl) (abs_nonneg (lam m-a)))
  rw [Real.norm_eq_abs]
  exact (abs_sub_le _ _ _).trans (add_le_add hBound le_rfl)

end ProphetSecretary.Model
