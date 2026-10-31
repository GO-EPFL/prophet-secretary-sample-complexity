import ProphetSecretary.Analysis.BregmanSecond

/-!
# Changing from duration weight to normalized reward weight

The map `z(λ)=(1-λ)/λ` changes a quadratic duration-regret coefficient by
`λ⁻³`. This calculation concerns the payoff of a fixed base policy.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

theorem tendsto_normalized_duration_quotient {F : ℝ → ℝ} {lam L : ℝ}
    (hlam : 0 < lam)
    (hF : Tendsto (fun k : ℝ ↦ F k / k ^ 2) (𝓝[≠] 0) (𝓝 L)) :
    Tendsto (fun h : ℝ ↦ (lam + h) * F (-h / (lam * (lam + h))) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (L / lam ^ 3)) := by
  let k : ℝ → ℝ := fun h ↦ -h / (lam * (lam + h))
  have hc : ContinuousAt k 0 := by
    fun_prop (disch := positivity)
  have hk0 : Tendsto k (𝓝 0) (𝓝 0) := by
    simpa only [k, neg_zero, add_zero, zero_div] using hc.tendsto
  have hne : ∀ᶠ h : ℝ in 𝓝[≠] 0, k h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds (show -lam < 0 by linarith)).filter_mono nhdsWithin_le_nhds] with h hh hp
    have hn : h ≠ 0 := by simpa using hh
    exact div_ne_zero (neg_ne_zero.mpr hn) (mul_ne_zero hlam.ne' (by linarith))
  have hk : Tendsto k (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [nhdsWithin]
    have hp : Tendsto k (𝓝[≠] 0) (𝓟 ({0}ᶜ : Set ℝ)) :=
      tendsto_principal.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using hne)
    have hk' : Tendsto k (𝓝[≠] 0) (𝓝 0) := hk0.mono_left nhdsWithin_le_nhds
    simpa only [inf_idem, nhdsWithin] using hk'.inf hp
  have hL := hF.comp hk
  have hfac : Tendsto (fun h : ℝ ↦ 1 / (lam ^ 2 * (lam + h))) (𝓝[≠] 0) (𝓝 (1 / lam ^ 3)) := by
    have hc : ContinuousAt (fun h : ℝ ↦ 1 / (lam ^ 2 * (lam + h))) 0 := by fun_prop (disch := positivity)
    have ht : Tendsto (fun h : ℝ ↦ 1 / (lam ^ 2 * (lam + h))) (𝓝[≠] 0)
        (𝓝 (1 / (lam ^ 2 * (lam + 0)))) := hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [add_zero, pow_succ] using ht
  have hprod := hL.mul hfac
  apply Filter.Tendsto.congr' _ (by simpa only [div_eq_mul_inv, one_mul] using hprod)
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds (show -lam < 0 by linarith)).filter_mono nhdsWithin_le_nhds] with h hh hp
  have hn : h ≠ 0 := by simpa using hh
  have hlh : lam + h ≠ 0 := by linarith
  dsimp only [Function.comp_apply, k]
  field_simp [hlam.ne', hlh, hn]

end ProphetSecretary.Analysis
