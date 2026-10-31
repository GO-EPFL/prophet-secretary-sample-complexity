import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Passing an outcome modulus through vanishing truncation errors
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma outcome_error_le_of_truncations {E r w δ : ℝ} {m e : ℕ → ℝ} {ω : ℝ → ℝ}
    (hr : 0 ≤ r) (hMono : Monotone ω) (hZero : ω 0=0)
    (hLimit : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hm : Tendsto m atTop (𝓝 (0 : ℝ))) (he : Tendsto e atTop (𝓝 (0 : ℝ)))
    (hBound : ∀ N, E ≤ (2*r+3*m N)/δ+ω (r+w*m N)+e N) :
    E ≤ 2*r/δ+ω (2*r) := by
  have hSmall : ∀ η > 0, E ≤ 2*r/δ+ω (r+η) := by
    intro η hη
    have hwm : Tendsto (fun N => w*m N) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hm.const_mul w
    have hEventually : ∀ᶠ N in atTop, w*m N < η := hwm.eventually (gt_mem_nhds hη)
    have hRight : Tendsto (fun N => (2*r+3*m N)/δ+ω (r+η)+e N) atTop
        (𝓝 (2*r/δ+ω (r+η))) := by
      simpa only [mul_zero,add_zero] using
        (((tendsto_const_nhds.add (hm.const_mul 3)).div_const δ).add_const (ω (r+η))).add he
    exact ge_of_tendsto hRight (hEventually.mono (fun N hN =>
      (hBound N).trans (add_le_add (add_le_add le_rfl (hMono (by linarith))) le_rfl)))
  by_cases hr0 : r=0
  · have hE : E ≤ 0 := by
      apply ge_of_tendsto hLimit
      filter_upwards [self_mem_nhdsWithin] with η hη
      simpa only [hr0,mul_zero,zero_div,zero_add] using hSmall η hη
    simpa only [hr0,mul_zero,zero_div,hZero,zero_add] using hE
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    simpa only [two_mul] using hSmall r hrp

lemma enlarged_outcome_modulus {H δ : ℝ} {ω : ℝ → ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hω : ∀ r, 0 ≤ ω r)
    (hMono : Monotone ω) (hZero : ω 0=0)
    (hLimit : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    let Ω := fun r : ℝ => min (H+1) (2*max r 0/δ+ω (2*r))
    (∀ r, 0 ≤ Ω r ∧ Ω r ≤ H+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let Ω := fun r : ℝ => min (H+1) (2*max r 0/δ+ω (2*r))
  have hDouble : Tendsto (fun r : ℝ => 2*r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hCont : Continuous (fun r : ℝ => 2*r) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hCont.tendsto (0 : ℝ)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos (show (0 : ℝ) < 2 by norm_num) hr
  have hLinear : Tendsto (fun r : ℝ => 2*max r 0/δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hm : Tendsto (fun r : ℝ => max r 0) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hCont : Continuous (fun r : ℝ => max r 0) := continuous_id.max continuous_const
      simpa only [max_self] using (hCont.tendsto (0 : ℝ)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [mul_zero,zero_div] using (hm.const_mul 2).div_const δ
  refine ⟨?_,?_,?_,?_⟩
  · intro r
    exact ⟨le_min (by linarith) (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hδ.le) (hω _)),min_le_left _ _⟩
  · intro x y hxy
    exact min_le_min le_rfl (add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (max_le_max hxy le_rfl) (by norm_num)) hδ.le)
      (hMono (mul_le_mul_of_nonneg_left hxy (by norm_num))))
  · simp only [max_self,mul_zero,zero_div,hZero,zero_add]
    exact min_eq_right (by linarith)
  · have hConst : Tendsto (fun _ : ℝ => H+1) (𝓝[>] (0 : ℝ)) (𝓝 (H+1)) := tendsto_const_nhds
    have h := hConst.min (hLinear.add (hLimit.comp hDouble))
    simpa only [Function.comp_def,zero_add,min_eq_right (show (0 : ℝ) ≤ H+1 by linarith)] using h

end ProphetSecretary.Analysis
