import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic affine support from a Lipschitz derivative

Subtracting a function with a Lipschitz derivative from `Kx²/2` gives a convex
function. Its supporting-line inequality gives the exact quadratic remainder
constant `K/2`, in either direction along the interval.
-/

open Set

namespace ProphetSecretary.Analysis

lemma convex_affine_support {S : Set ℝ} {f g : ℝ → ℝ}
    (hc : ConvexOn ℝ S f) (hf : ∀ x ∈ S, HasDerivAt f (g x) x)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    0 ≤ f y - f x - (y - x) * g x := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hc.le_slope_of_hasDerivAt hx hy hxy (hf x hx)
    rw [slope_def_field] at h
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    nlinarith
  · simp
  · have h := hc.slope_le_of_hasDerivAt hy hx hyx (hf x hx)
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

lemma convex_quadratic_sub_of_deriv_lipschitz {S : Set ℝ} {f g : ℝ → ℝ} {K : ℝ}
    (hS : Convex ℝ S) (hf : ∀ x ∈ S, HasDerivAt f (g x) x)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, |g y - g x| ≤ K * |y - x|) :
    ConvexOn ℝ S (fun x ↦ K * x ^ 2 / 2 - f x) := by
  let E : ℝ → ℝ := fun x ↦ K * x ^ 2 / 2 - f x
  have hE : ∀ x ∈ S, HasDerivAt E (K * x - g x) x := by
    intro x hx
    have h := ((((hasDerivAt_id x).pow 2).const_mul K).div_const 2).sub (hf x hx)
    convert h using 1 <;> try rfl
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  apply MonotoneOn.convexOn_of_deriv hS
    (fun x hx ↦ (hE x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hE x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(hE x (interior_subset hx)).deriv, (hE y (interior_subset hy)).deriv]
  have h := (le_abs_self (g y - g x)).trans (hLip x (interior_subset hx) y (interior_subset hy))
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at h
  linarith

/-- Exact two-sided quadratic support, with the sharp `K/2` constant. -/
theorem quadratic_support_of_deriv_lipschitz {S : Set ℝ} {f g : ℝ → ℝ} {K : ℝ}
    (hc : ConvexOn ℝ S f) (hf : ∀ x ∈ S, HasDerivAt f (g x) x)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, |g y - g x| ≤ K * |y - x|)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    0 ≤ f y - f x - (y - x) * g x ∧
      f y - f x - (y - x) * g x ≤ K * (y - x) ^ 2 / 2 := by
  refine ⟨convex_affine_support hc hf hx hy, ?_⟩
  have hconv := convex_quadratic_sub_of_deriv_lipschitz hc.1 hf hLip
  have hDeriv : ∀ t ∈ S, HasDerivAt (fun v ↦ K * v ^ 2 / 2 - f v) (K * t - g t) t := by
    intro t ht
    convert ((((hasDerivAt_id t).pow 2).const_mul K).div_const 2).sub (hf t ht) using 1 <;> try rfl
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have h := convex_affine_support hconv hDeriv hx hy
  nlinarith

end ProphetSecretary.Analysis
