import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The triangular loss at a moving threshold

Integrating the first-order expansion of a continuation value gives a quadratic
Peano expansion of its primitive. Oriented interval integrals handle both signs
of the parameter change in one formula.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace ProphetSecretary.Analysis

/-- The primitive of a differentiable function has the corresponding quadratic
expansion, with a complete little-o remainder. -/
theorem integral_peano_two {f : ℝ → ℝ} (hf : Continuous f) {d T : ℝ} (hD : HasDerivAt f T d) :
    (fun y ↦ (∫ t in d..y, f t - f d) - T * (y - d) ^ 2 / 2) =o[𝓝 d]
      (fun y ↦ (y - d) ^ 2) := by
  let E : ℝ → ℝ := fun t ↦ f t - f d - (t - d) * T
  let H : ℝ → ℝ := fun y ↦ ∫ t in d..y, E t
  have hEcont : Continuous E :=
    (hf.sub continuous_const).sub ((continuous_id.sub continuous_const).mul continuous_const)
  have hH : ∀ y : ℝ, HasDerivAt H (E y) y := by
    intro y
    have hmeas : StronglyMeasurableAtFilter E (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_univ hEcont.continuousOn y (mem_univ y)
    exact intervalIntegral.integral_hasDerivAt_right (hEcont.intervalIntegrable d y) hmeas hEcont.continuousAt
  have hELittle : E =o[𝓝 d] (fun y ↦ y - d) := by
    simpa only [E, smul_eq_mul] using hD.isLittleO
  have hLift := (convex_univ : Convex ℝ (univ : Set ℝ)).isLittleO_pow_succ_real
    (x₀ := d) (n := 1) (mem_univ d) (fun y _hy ↦ (hH y).hasDerivWithinAt)
    (by simpa only [nhdsWithin_univ, pow_one] using hELittle)
  have hPrimitive : H =o[𝓝 d] (fun y ↦ (y - d) ^ 2) := by
    simpa only [H, intervalIntegral.integral_same, sub_zero, nhdsWithin_univ, Nat.reduceAdd] using hLift
  apply hPrimitive.congr_left
  intro y
  have hlin : (∫ t in d..y, (t - d) * T) = T * (y - d) ^ 2 / 2 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun t : ℝ ↦ t) (g := fun _ : ℝ ↦ d)
        (continuous_id.intervalIntegrable d y) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    ring
  have hI := intervalIntegral.integral_sub (μ := volume) (f := fun t ↦ f t - f d) (g := fun t ↦ (t - d) * T)
    ((hf.sub continuous_const).intervalIntegrable d y)
    (((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable d y)
  change (∫ t in d..y, (f t - f d) - (t - d) * T) = _
  exact hI.trans (congrArg ((∫ t in d..y, f t - f d) - ·) hlin)

/-- The primitive's quadratic coefficient along any affine displacement. -/
theorem tendsto_integral_triangle_quotient {f : ℝ → ℝ} (hf : Continuous f)
    {d T k : ℝ} (hD : HasDerivAt f T d) :
    Tendsto (fun h : ℝ ↦ (∫ t in d..(d + k * h), f t - f d) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (T * k ^ 2 / 2)) := by
  have hcont : Continuous (fun h : ℝ ↦ d + k * h) := continuous_const.add (continuous_const.mul continuous_id)
  have ht : Tendsto (fun h : ℝ ↦ d + k * h) (𝓝 0) (𝓝 d) := by
    simpa only [mul_zero, add_zero] using hcont.tendsto 0
  have hComp := (integral_peano_two hf hD).comp_tendsto ht
  have hRem : (fun h : ℝ ↦ (∫ t in d..(d + k * h), f t - f d) - T * (k * h) ^ 2 / 2) =o[𝓝 0]
      (fun h ↦ k ^ 2 * h ^ 2) := by
    convert hComp using 1 <;> funext h <;> simp only [Function.comp_apply] <;> ring
  have hSmall : (fun h : ℝ ↦ (∫ t in d..(d + k * h), f t - f d) - T * (k * h) ^ 2 / 2) =o[𝓝 0]
      (fun h ↦ h ^ 2) := hRem.of_const_mul_right
  have hLim : Tendsto (fun h : ℝ ↦
      ((∫ t in d..(d + k * h), f t - f d) - T * (k * h) ^ 2 / 2) / h ^ 2)
      (𝓝[≠] 0) (𝓝 0) := hSmall.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hAdd := hLim.add_const (T * k ^ 2 / 2)
  have hAdd' : Tendsto (fun h : ℝ ↦
      ((∫ t in d..(d + k * h), f t - f d) - T * (k * h) ^ 2 / 2) / h ^ 2 + T * k ^ 2 / 2)
      (𝓝[≠] 0) (𝓝 (T * k ^ 2 / 2)) := by simpa only [zero_add] using hAdd
  apply hAdd'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  field_simp [hne]
  ring

/-- The exact moving-root primitive includes the Jacobian `1/(z+h)`.
Its coefficient is the boundary-Hessian triangular loss. -/
theorem tendsto_moving_triangle_quotient {f : ℝ → ℝ} (hf : Continuous f)
    {d T z : ℝ} (hD : HasDerivAt f T d) (hz : 0 < z) :
    Tendsto (fun h : ℝ ↦ ((∫ t in d..(d + (d / z) * h), f t - f d) / (z + h)) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (d ^ 2 * T / (2 * z ^ 3))) := by
  have hq := tendsto_integral_triangle_quotient (k := d / z) hf hD
  have hi : Tendsto (fun h : ℝ ↦ (z + h)⁻¹) (𝓝[≠] 0) (𝓝 z⁻¹) := by
    have hc : Continuous (fun h : ℝ ↦ z + h) := continuous_const.add continuous_id
    have hbase : Tendsto (fun h : ℝ ↦ z + h) (𝓝 0) (𝓝 z) := by
      simpa only [add_zero] using hc.tendsto 0
    exact (hbase.inv₀ hz.ne').mono_left nhdsWithin_le_nhds
  have hmul := hi.mul hq
  convert hmul using 1
  · funext h
    ring
  · field_simp [hz.ne']

end ProphetSecretary.Analysis
