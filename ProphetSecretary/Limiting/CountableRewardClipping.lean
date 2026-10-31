import ProphetSecretary.Limiting.CountableCapValueContinuity
import ProphetSecretary.Limiting.CountableCapExcessConvergence
import ProphetSecretary.Limiting.HybridRewardClipping

/-!
# Actual reward-only clipping in the full countable model

First the finite Bernoulli limit establishes clipping for each finite-intensity
truncation. Then retained dimension and the omitted-band cutoff converge.
Positive-band domination controls moving excess moments, and the uniform
cap-height bound transfers the optimized capped values. No optimizer, policy,
score, or derivative convergence is inferred from these value limits.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting.CountableInstance

/-- The full countable reward-boundary clipping inequality, including infinitely
many anonymous marks near zero and arbitrary atoms at the optimized cap. -/
theorem reward_clipping_value_le (B : CountableInstance) (hZero : B.terminal=0)
    (hV : 0<B.optimalScalarValue 1 0) :
    let K : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hV.le⟩
    (B.capAt hZero K hV).optimalScalarValue 1 (B.totalCapExcess K)≤B.optimalScalarValue 1 0 := by
  let K : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hV.le⟩
  have hK : 0<K := hV
  let T := fun m => B.truncation m (B.markCutoff m) (B.terminal_lt_markCutoff m)
  let hs : ℕ → ℝ≥0 := fun m => ⟨(T m).optimalScalarValue 1 0,(T m).optimalScalarValue_nonnegative zero_le_one le_rfl⟩
  have hVLim : Tendsto (fun m => (T m).optimalScalarValue 1 0) atTop (𝓝 (B.optimalScalarValue 1 0)) :=
    B.truncation_value_tendsto id B.markCutoff B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto zero_le_one le_rfl
  have hHeightLim : Tendsto hs atTop (𝓝 K) := by
    apply NNReal.tendsto_coe.1
    exact hVLim
  let Ks := fun m => max (hs m) (K/2)
  have hKs (m : ℕ) : 0<Ks m := (half_pos hK).trans_le (le_max_right _ _)
  have hKsLim : Tendsto Ks atTop (𝓝 K) := by
    simpa only [max_eq_left (half_lt_self hK).le] using
      hHeightLim.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => K/2) atTop (𝓝 (K/2)))
  have hSame : ∀ᶠ m in atTop, Ks m=hs m := by
    filter_upwards [hHeightLim.eventually (Ioi_mem_nhds (half_lt_self hK))] with m hm
    exact max_eq_left hm.le
  have hELim : Tendsto (fun m => (T m).totalCapExcess (Ks m)) atTop (𝓝 (B.totalCapExcess K)) :=
    B.truncation_totalCapExcess_tendsto_moving hZero id B.markCutoff B.terminal_lt_markCutoff
      tendsto_id B.markCutoff_tendsto hK hKsLim
  have hCapped : Tendsto (fun m => ((T m).capAt (Ks m) (hKs m)).optimalScalarValue 1 ((T m).totalCapExcess (Ks m))) atTop
      (𝓝 ((B.capAt hZero K hK).optimalScalarValue 1 (B.totalCapExcess K))) :=
    B.capped_truncation_value_tendsto_moving hZero id B.markCutoff B.terminal_lt_markCutoff
      tendsto_id B.markCutoff_tendsto hKs hK hKsLim
      (fun m => (T m).totalCapExcess_nonnegative (Ks m)) (B.totalCapExcess_nonnegative K) zero_lt_one hELim
  have hClip : ∀ᶠ m in atTop,
      ((T m).capAt (Ks m) (hKs m)).optimalScalarValue 1 ((T m).totalCapExcess (Ks m))≤(T m).optimalScalarValue 1 0 := by
    filter_upwards [hSame] with m hm
    have hHs : 0<hs m := (hKs m).trans_eq hm
    have hVm : 0<(T m).optimalScalarValue 1 0 := by exact_mod_cast hHs
    have hFinite : ((T m).capAt (hs m) hHs).optimalScalarValue 1 ((T m).totalCapExcess (hs m))≤(T m).optimalScalarValue 1 0 :=
      (T m).reward_clipping_value_le hZero hVm
    have hCapEq : (⟨Ks m,hKs m⟩ : {L : ℝ≥0 // 0<L})=⟨hs m,hHs⟩ := Subtype.ext hm
    have hValueEq := congrArg (fun L : {L : ℝ≥0 // 0<L} =>
      ((T m).capAt L.val L.property).optimalScalarValue 1 ((T m).totalCapExcess L.val)) hCapEq
    exact hValueEq.trans_le hFinite
  exact le_of_tendsto_of_tendsto hCapped hVLim hClip

end ProphetSecretary.Limiting.CountableInstance
