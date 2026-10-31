import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Pointwise limits with a common local Lipschitz derivative bound

A finite pointwise limit retains the local C^{1,1} bound. Derivatives are first
shown Cauchy using a common quadratic remainder and converging difference
quotients. This avoids inferring derivative convergence from value convergence
alone. Paper correspondence: the pointwise-limit clause of `thm:scalar-curvature`.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma quadratic_remainder_of_lipschitz_derivative {f g : ℝ → ℝ} {a b x y : ℝ} {K : NNReal}
    (hf : ∀ z ∈ Icc a b, HasDerivAt f (g z) z) (hg : LipschitzOnWith K g (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f y - f x - g x * (y - x)| ≤ (K : ℝ) * (y - x) ^ 2 := by
  let F : ℝ → ℝ := fun z => f z - f x - g x * (z - x)
  have hsubset : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  have hF (z : ℝ) (hz : z ∈ uIcc x y) :
      HasDerivWithinAt F (g z - g x) (uIcc x y) z := by
    have hd := ((hf z (hsubset hz)).sub_const (f x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (g x))
    have heq : ((fun t => f t - f x) - fun t => g x * (id t - x)) = F := by
      funext t
      rfl
    rw [heq] at hd
    simpa only [one_mul, mul_one] using hd.hasDerivWithinAt
  have hbound (z : ℝ) (hz : z ∈ uIcc x y) :
      ‖g z - g x‖ ≤ (K : ℝ) * |y - x| := by
    have h := hg.dist_le_mul z (hsubset hz) x hx
    have hzDist : dist z x ≤ dist y x := by
      simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hz
    exact h.trans (mul_le_mul_of_nonneg_left hzDist K.coe_nonneg)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF hbound
    (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
  dsimp [F] at h
  simp only [sub_self, mul_zero, sub_zero] at h
  have heq : (K : ℝ) * |y - x| * |y - x| = (K : ℝ) * (y - x) ^ 2 := by
    rw [mul_assoc, ← pow_two, sq_abs]
  exact h.trans_eq heq

lemma slope_approximation_of_quadratic {f g : ℝ → ℝ} {x h K : ℝ} (hh : 0 < h)
    (hquad : |f (x + h) - f x - g x * ((x + h) - x)| ≤ K * ((x + h) - x) ^ 2) :
    |(f (x + h) - f x) / h - g x| ≤ K * h := by
  have heq : (f (x + h) - f x) / h - g x =
      (f (x + h) - f x - g x * ((x + h) - x)) / h := by field_simp; ring
  rw [heq, abs_div, abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using hquad

/-- A common quadratic remainder and pointwise value convergence force derivative
convergence at each interior point; mere value convergence is not used alone. -/
theorem cauchy_derivatives_of_quadratic {f g : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    {a b x K : ℝ} (hK : 0 ≤ K) (hx : x ∈ Ioo a b)
    (hquad : ∀ m z, z ∈ Icc a b → ∀ y, y ∈ Icc a b →
      |f m y - f m z - g m z * (y - z)| ≤ K * (y - z) ^ 2)
    (hlimit : ∀ z ∈ Icc a b, Tendsto (fun m => f m z) atTop (𝓝 (F z))) :
    CauchySeq (fun m => g m x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let h := min ((b - x) / 2) (ε / (8 * (K + 1)))
  have hh : 0 < h := by dsimp [h]; exact lt_min (by linarith [hx.2]) (by positivity)
  have hxh : x + h ∈ Icc a b := by
    have hb := min_le_left ((b - x) / 2) (ε / (8 * (K + 1)))
    constructor <;> dsimp [h] at * <;> linarith [hx.1]
  have hKh : 2 * K * h ≤ ε / 4 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 8 * (K + 1))).mp
      (min_le_right ((b - x) / 2) (ε / (8 * (K + 1))))
    change h * (8 * (K + 1)) ≤ ε at hs
    nlinarith
  let slope : ℕ → ℝ := fun m => (f m (x + h) - f m x) / h
  have hslimit : Tendsto slope atTop (𝓝 ((F (x + h) - F x) / h)) :=
    ((hlimit (x + h) hxh).sub (hlimit x ⟨hx.1.le, hx.2.le⟩)).div_const h
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hslimit.cauchySeq (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmApprox := slope_approximation_of_quadratic hh (hquad m x ⟨hx.1.le, hx.2.le⟩ (x + h) hxh)
  have hnApprox := slope_approximation_of_quadratic hh (hquad n x ⟨hx.1.le, hx.2.le⟩ (x + h) hxh)
  have hmid := hN m hm n hn
  have htriangle := dist_triangle4 (g m x) (slope m) (slope n) (g n x)
  simp only [Real.dist_eq] at hmid htriangle ⊢
  have hmBound : |g m x - slope m| ≤ K * h := by
    simpa only [slope, abs_sub_comm] using hmApprox
  have hnBound : |slope n - g n x| ≤ K * h := hnApprox
  linarith

/-- Passing the quadratic remainder to a derivative limit gives genuine
differentiability of the pointwise value limit. -/
theorem hasDerivAt_pointwise_limit_of_quadratic {f g : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    {a b x K G : ℝ} (hK : 0 ≤ K) (hx : x ∈ Ioo a b)
    (hquad : ∀ m y, y ∈ Icc a b →
      |f m y - f m x - g m x * (y - x)| ≤ K * (y - x) ^ 2)
    (hlimit : ∀ z ∈ Icc a b, Tendsto (fun m => f m z) atTop (𝓝 (F z)))
    (hderivLimit : Tendsto (fun m => g m x) atTop (𝓝 G)) : HasDerivAt F G x := by
  have hquadF (y : ℝ) (hy : y ∈ Icc a b) :
      |F y - F x - G * (y - x)| ≤ K * (y - x) ^ 2 := by
    have ht := (((hlimit y hy).sub (hlimit x ⟨hx.1.le, hx.2.le⟩)).sub
      (hderivLimit.mul_const (y - x))).abs
    exact le_of_tendsto ht (Eventually.of_forall fun m => hquad m y hy)
  apply hasDerivAt_iff_isLittleO.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  let d := ε / (K + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [Icc_mem_nhds hx.1 hx.2,
    Ioo_mem_nhds (sub_lt_self x hd) (lt_add_of_pos_right x hd)] with y hy hySmall
  have hdist : |y - x| ≤ d := by
    rw [abs_le]
    constructor <;> linarith [hySmall.1, hySmall.2]
  have hcoef : K * |y - x| ≤ ε := by
    have ht := (le_div_iff₀ (by positivity : 0 < K + 1)).mp hdist
    nlinarith [abs_nonneg (y - x)]
  have hbound : K * (y - x) ^ 2 ≤ ε * |y - x| := by
    have ht := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (y - x))
    nlinarith [sq_abs (y - x)]
  have heq : (y - x) * G = G * (y - x) := mul_comm _ _
  simpa only [Real.norm_eq_abs, smul_eq_mul, heq] using (hquadF y hy).trans hbound

/-- A pointwise limit on `(0,1)` inherits every common local Lipschitz bound
for derivatives. The constants may vary with the closed interior interval. -/
theorem pointwise_limit_local_C11 (f g : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (K : ℝ → ℝ → NNReal)
    (hderiv : ∀ m x, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt (f m) (g m x) x)
    (hLip : ∀ m a b, 0 < a → b < 1 → LipschitzOnWith (K a b) (g m) (Icc a b))
    (hlimit : ∀ x ∈ Ioo (0 : ℝ) 1, Tendsto (fun m => f m x) atTop (𝓝 (F x))) :
    (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (deriv F x) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, Tendsto (fun m => g m x) atTop (𝓝 (deriv F x))) ∧
      ∀ a b, 0 < a → b < 1 → LipschitzOnWith (K a b) (deriv F) (Icc a b) := by
  have hlocal (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (deriv F x) x ∧
        Tendsto (fun m => g m x) atTop (𝓝 (deriv F x)) := by
    let a := x / 2
    let b := (x + 1) / 2
    have ha : 0 < a := by dsimp [a]; linarith [hx.1]
    have hb : b < 1 := by dsimp [b]; linarith [hx.2]
    have hx' : x ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith [hx.1, hx.2]
    have hsubset : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun _ hz =>
      ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
    have hquad : ∀ m z, z ∈ Icc a b → ∀ y, y ∈ Icc a b →
        |f m y - f m z - g m z * (y - z)| ≤ (K a b : ℝ) * (y - z) ^ 2 := by
      intro m z hz y hy
      exact quadratic_remainder_of_lipschitz_derivative
        (fun t ht => hderiv m t (hsubset ht)) (hLip m a b ha hb) hz hy
    have hlimLocal := fun z hz => hlimit z (hsubset hz)
    have hGlim := (cauchy_derivatives_of_quadratic (K a b).coe_nonneg hx' hquad hlimLocal).tendsto_limUnder
    have hF := hasDerivAt_pointwise_limit_of_quadratic (K a b).coe_nonneg hx'
      (fun m y hy => hquad m x ⟨hx'.1.le, hx'.2.le⟩ y hy) hlimLocal hGlim
    rw [← hF.deriv] at hGlim hF
    exact ⟨hF, hGlim⟩
  refine ⟨fun x hx => (hlocal x hx).1, fun x hx => (hlocal x hx).2, ?_⟩
  intro a b ha hb
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 : x ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hy0 : y ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩
  have ht := ((hlocal x hx0).2.prodMk_nhds (hlocal y hy0).2)
  exact le_of_tendsto (continuous_dist.tendsto _ |>.comp ht)
    (Eventually.of_forall fun m => (hLip m a b ha hb).dist_le_mul x hx y hy)

end ProphetSecretary.Analysis
