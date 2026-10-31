import ProphetSecretary.Probability.WideFrozenInformationTaylor
import Mathlib.Analysis.Calculus.MeanValue

/-! # Curvature of the prophet benchmark under likelihood perturbations
The maximum is a bounded complete-vector analytical payoff. Its differentiation
does not grant future information to any online policy.
-/
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ}

theorem expectedMaximum_likelihoodWidePath_twice_differentiable (P : Instance n) {H : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let M := fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum
    DifferentiableAt ℝ M θ ∧ DifferentiableAt ℝ (deriv M) θ ∧
      |deriv (deriv M) θ| ≤ 8 * H * information P.law h := by
  let M := fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum
  have hAbs : |θ| ≤ 1 / 2 := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
  let Q := P.likelihoodWideTilt h hh hb hm θ hAbs
  have hQB := P.likelihoodWideTilt_bounded h hh hb hm θ hAbs hbound
  let s := fun i ↦ recenteredUnitScore (h i) θ
  have hsM (i : Fin n) : Measurable (s i) := measurable_recenteredUnitScore (hh i) θ
  have hsB (i : Fin n) : ∀ᵐ a ∂Q.law i, |s i a| ≤ 1 := recenteredUnitScore_bound (hb i) hAbs
  have hs0 (i : Fin n) : ∫ a, s i a ∂Q.law i = 0 := recenteredUnitScore_centered (hh i) (hb i) (hm i) hAbs
  have hFb : ∀ᵐ x ∂Q.valuesLaw, |maximum x| ≤ H :=
    (Q.values_bound_ae hQB).mono (fun x hx ↦ by rw [abs_of_nonneg (maximum_nonnegative x)]; exact maximum_le x hH hx)
  let r := fun t : ℝ ↦ 2 * (t - θ)
  let F := fun t ↦ fixedPayoffMean Q.law s maximum (r t)
  let G := fun t ↦ fixedPayoffFirst Q.law s maximum (r t) * 2
  have hInner (t : ℝ) : HasDerivAt r 2 t := by
    simpa only [r, id_eq, mul_one] using ((hasDerivAt_id t).sub_const θ).const_mul 2
  have hNear : ∀ᶠ t : ℝ in 𝓝 θ, |r t| ≤ 1 / 4 ∧ |t| ≤ 1 / 2 := by
    have hSmall : ∀ᶠ t : ℝ in 𝓝 θ, t ∈ Icc (θ - 1 / 8) (θ + 1 / 8) := Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [hSmall, Icc_mem_nhds hθ.1 hθ.2] with t ht hHalf
    exact ⟨abs_le.mpr ⟨by dsimp only [r]; linarith [ht.1], by dsimp only [r]; linarith [ht.2]⟩, abs_le.mpr hHalf⟩
  have hEq : M =ᶠ[𝓝 θ] F := by
    filter_upwards [hNear] with t ht
    have hAdd : θ + (t - θ) = t := by ring
    have hRebase := P.likelihoodWideTilt_rebase h hh hb hm hAbs ht.1
      (show |θ + (t - θ)| ≤ 1 / 2 by simpa only [hAdd] using ht.2)
    have hRebase' : Q.likelihoodTilt s hsM hsB hs0 (r t) ht.1 = P.likelihoodWidePath h hh hb hm t := by
      rw [P.likelihoodWidePath_of_mem h hh hb hm ht.2]
      simpa only [hAdd] using hRebase
    dsimp only [M]
    rw [← hRebase']
    change (∫ x, maximum x ∂productTiltLaw Q.law s (r t)) = fixedPayoffMean Q.law s maximum (r t)
    rw [integral_productTiltLaw Q.law s hsM hsB hs0 ht.1]
    unfold fixedPayoffMean
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ ↦ mul_comm _ _)
  have hPoly (t : ℝ) (ht : |r t| ≤ 1 / 4) : HasDerivAt F (G t) t :=
    ((fixedPayoff_derivatives Q.law s hsM hsB maximum measurable_maximum hH hFb ht).1).comp t (hInner t)
  have hr0 : r θ = 0 := by dsimp only [r]; ring
  have hD1 : HasDerivAt M (G θ) θ := (hPoly θ (by rw [hr0]; norm_num)).congr_of_eventuallyEq hEq
  have hDerivEq : deriv M =ᶠ[𝓝 θ] G := hEq.deriv.trans (hNear.mono (fun t ht ↦ (hPoly t ht.1).deriv))
  have hSec := (fixedPayoff_derivatives Q.law s hsM hsB maximum measurable_maximum hH hFb
    (by norm_num : |(0 : ℝ)| ≤ 1 / 4)).2
  have hSec' : HasDerivAt (fixedPayoffFirst Q.law s maximum) (fixedPayoffSecond Q.law s maximum 0) (r θ) := by
    simpa only [hr0] using hSec
  have hG : HasDerivAt G (fixedPayoffSecond Q.law s maximum 0 * 2 * 2) θ :=
    (hSec'.comp θ (hInner θ)).mul_const 2
  have hD2 := hG.congr_of_eventuallyEq hDerivEq
  have hInfoEq : information Q.law s = (1 / 4 : ℝ) * information Q.law (fun i ↦ tiltedScore (h i) θ) := by
    unfold information
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun a ↦ by dsimp only [s, recenteredUnitScore]; ring)
  have hInfo : information Q.law s ≤ (1 / 2 : ℝ) * information P.law h := by
    rw [hInfoEq]
    have hi := P.information_likelihoodWideTilt_tiltedScore_le h hh hb hm hAbs
    nlinarith
  have hSecBound := fixedPayoffSecond_abs_le Q.law s hsM hsB hs0 maximum measurable_maximum hH hFb
    (by norm_num : |(0 : ℝ)| ≤ 1 / 4)
  refine ⟨hD1.differentiableAt, hD2.differentiableAt, ?_⟩
  rw [hD2.deriv, abs_mul, abs_mul]
  norm_num only [show |(2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ (4 * H * information Q.law s) * 2 * 2 := by nlinarith
    _ = (16 * H) * information Q.law s := by ring
    _ ≤ (16 * H) * ((1 / 2 : ℝ) * information P.law h) := mul_le_mul_of_nonneg_left hInfo (by positivity)
    _ = _ := by ring

/-- The benchmark derivative has a dimension-free information Lipschitz bound. -/
theorem expectedMaximum_likelihoodWidePath_deriv_lipschitz (P : Instance n) {H : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) (hρ : ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    |deriv (fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum) ρ -
      deriv (fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum) θ| ≤
      (8 * H * information P.law h) * |ρ - θ| := by
  have hHalf (t : ℝ) (ht : t ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    constructor <;> linarith [ht.1, ht.2]
  have hM := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ ((P.expectedMaximum_likelihoodWidePath_twice_differentiable hH hbound h hh hb hm (hHalf t ht)).2.1.hasDerivAt.hasDerivWithinAt))
    (fun t ht ↦ by simpa only [Real.norm_eq_abs] using (P.expectedMaximum_likelihoodWidePath_twice_differentiable hH hbound h hh hb hm (hHalf t ht)).2.2)
    (convex_Icc (-(1 / 4) : ℝ) (1 / 4)) hθ hρ
  simpa only [Real.norm_eq_abs] using hM

end ProphetSecretary.Model.Instance
