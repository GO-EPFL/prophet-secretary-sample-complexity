import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# The two-limit stability sandwich for original-instance score expectations

First the finite-instance index tends to infinity at a fixed coarse policy.
Only then is that policy refined. The stability modulus need be monotone
and continuous from the right at zero; continuity at a positive coarse
regret is not assumed. Paper correspondence: the last comparison step in
`updual:scorelift`.
-/

open Set Filter
open scoped Topology
namespace ProphetSecretary.Analysis

theorem tendsto_of_twoLimit_scoreStability {a : ℕ → ℝ} {coarse : ℕ → ℕ → ℝ}
    {b r : ℕ → ℝ} {target C : ℝ} {regret : ℕ → ℕ → ℝ} {Ω : ℝ → ℝ}
    (hC : 0≤C) (hMono : Monotone Ω) (hOmega : Tendsto Ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hCoarse : ∀ j, Tendsto (coarse j) atTop (𝓝 (b j)))
    (hTarget : Tendsto b atTop (𝓝 target))
    (hRegret : ∀ j, Tendsto (regret j) atTop (𝓝 (r j)))
    (hRefine : Tendsto r atTop (𝓝 (0 : ℝ)))
    (hCompare : ∀ j, ∀ᶠ m in atTop, |a m-coarse j m|≤Real.sqrt (C*Ω (regret j m))) :
    Tendsto a atTop (𝓝 target) := by
  have hInner : Tendsto (fun x => C*Ω x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hOmega.const_mul C
  have hRoot : Tendsto (fun x => Real.sqrt (C*Ω x)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hInner
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hThird : 0<ε/3 := by linarith only [hε]
  obtain ⟨η,hSmall,hη⟩ := ((hRoot.eventually (gt_mem_nhds hThird)).and self_mem_nhdsWithin).exists
  obtain ⟨j,hRj,hBj⟩ := ((hRefine.eventually (gt_mem_nhds hη)).and
    (hTarget.eventually (Metric.ball_mem_nhds target hThird))).exists
  filter_upwards [hCompare j,hRegret j |>.eventually (gt_mem_nhds hRj),
    hCoarse j |>.eventually (Metric.ball_mem_nhds (b j) hThird)] with m hComp hR hNear
  have hError : |a m-coarse j m|<ε/3 := hComp.trans_lt
    ((Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hMono hR.le) hC)).trans_lt hSmall)
  have hNearCoarse : |coarse j m-b j|<ε/3 := by simpa only [Metric.mem_ball,Real.dist_eq] using hNear
  have hNearTarget : |b j-target|<ε/3 := by simpa only [Metric.mem_ball,Real.dist_eq] using hBj
  have hTriangle : |a m-target|≤|a m-coarse j m|+(|coarse j m-b j|+|b j-target|) :=
    (abs_sub_le _ _ _).trans (add_le_add le_rfl (abs_sub_le _ _ _))
  rw [Real.dist_eq]
  linarith only [hError,hNearCoarse,hNearTarget,hTriangle]

end ProphetSecretary.Analysis
