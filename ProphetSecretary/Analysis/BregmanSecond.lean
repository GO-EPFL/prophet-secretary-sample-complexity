import ProphetSecretary.Analysis.TriangularRegret
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Convex.Deriv

/-!
# Second-order supporting-payoff quotients

At a differentiability point of the first derivative, the supporting affine
remainder has quadratic coefficient one half of the second derivative. The
argument uses a Peano remainder and requires no continuous second derivative.
-/

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace ProphetSecretary.Analysis

theorem bregman_peano_two {f g : ℝ → ℝ} {a b x D : ℝ} (hx : x ∈ Ioo a b)
    (hf : ∀ y ∈ Ioo a b, HasDerivAt f (g y) y) (hg : HasDerivAt g D x) :
    (fun y ↦ f y - f x - (y - x) * g x - D * (y - x) ^ 2 / 2) =o[𝓝 x]
      (fun y ↦ (y - x) ^ 2) := by
  let E : ℝ → ℝ := fun y ↦ g y - g x - (y - x) * D
  let H : ℝ → ℝ := fun y ↦ f y - f x - (y - x) * g x - D * (y - x) ^ 2 / 2
  have hD : ∀ y ∈ Ioo a b, HasDerivWithinAt H (E y) (Ioo a b) y := by
    intro y hy
    have hl := ((hasDerivAt_id y).sub_const x).mul_const (g x)
    have hq := ((((hasDerivAt_id y).sub_const x).pow 2).const_mul D).div_const 2
    have h := (((hf y hy).sub_const (f x)).sub hl).sub hq
    apply HasDerivAt.hasDerivWithinAt
    convert h using 1
    · funext v
      simp only [H, Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [E, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, one_mul]
      ring
  have hE : E =o[𝓝 x] (fun y ↦ y - x) := by
    simpa only [E, smul_eq_mul] using hg.isLittleO
  have hLift := (convex_Ioo a b).isLittleO_pow_succ_real (x₀ := x) (n := 1) hx hD
    (by simpa only [nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds hx.1 hx.2), pow_one] using hE)
  simpa only [H, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div, sub_zero, nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds hx.1 hx.2), Nat.reduceAdd] using hLift

theorem tendsto_bregman_quotient {f g : ℝ → ℝ} {a b x D : ℝ} (hx : x ∈ Ioo a b)
    (hf : ∀ y ∈ Ioo a b, HasDerivAt f (g y) y) (hg : HasDerivAt g D x) :
    Tendsto (fun h : ℝ ↦ (f (x + h) - f x - h * g x) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (D / 2)) := by
  have hc : Continuous (fun h : ℝ ↦ x + h) := continuous_const.add continuous_id
  have ht : Tendsto (fun h : ℝ ↦ x + h) (𝓝 0) (𝓝 x) := by
    simpa only [add_zero] using hc.tendsto 0
  have hO := (bregman_peano_two hx hf hg).comp_tendsto ht
  have hSmall : (fun h : ℝ ↦ f (x + h) - f x - h * g x - D * h ^ 2 / 2) =o[𝓝 0]
      (fun h ↦ h ^ 2) := by
    convert hO using 1 <;> funext h <;> simp only [Function.comp_apply] <;> ring
  have hLim : Tendsto (fun h : ℝ ↦
      (f (x + h) - f x - h * g x - D * h ^ 2 / 2) / h ^ 2) (𝓝[≠] 0) (𝓝 0) :=
    hSmall.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hAdd := hLim.add_const (D / 2)
  apply Filter.Tendsto.congr' _ (by simpa only [zero_add] using hAdd)
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn : h ≠ 0 := by simpa using hh
  field_simp [hn]
  ring

/-- Convex differentiable scalar objectives have a second derivative almost
everywhere on their open weight interval. -/
theorem convex_ae_secondDerivative {f : ℝ → ℝ} {a b : ℝ}
    (hconv : ConvexOn ℝ (Ioo a b) f)
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), DifferentiableAt ℝ (deriv f) x := by
  filter_upwards [(hconv.monotoneOn_deriv hf).ae_differentiableWithinAt measurableSet_Ioo,
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  exact hx.differentiableAt (Ioo_mem_nhds hmem.1 hmem.2)

end ProphetSecretary.Analysis
