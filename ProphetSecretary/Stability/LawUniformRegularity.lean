import ProphetSecretary.Stability.LawHessian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Uniform finite law regularity on the closed manuscript interval
The preliminary finite Lipschitz estimate supplies absolute continuity.
Integrating the dimension-free almost-everywhere Hessian estimate removes its
cardinality dependence and includes both quarter-interval endpoints.
-/
open MeasureTheory Set
open scoped Topology NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.lawValue_deriv_lipschitz_information (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) (hρ : ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    |deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) ρ -
      deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
      ((8 * (w * H + c) + 6 * w ^ 2 * H * P.totalFirstMoment / c) * information P.law h) * |ρ - θ| := by
  let f := fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c
  let g := deriv f
  have hQuarter : uIcc θ ρ ⊆ Icc (-(1 / 4) : ℝ) (1 / 4) := by
    intro t ht
    exact ⟨(le_min hθ.1 hρ.1).trans ht.1, ht.2.trans (max_le hθ.2 hρ.2)⟩
  obtain ⟨L, _hL, hLip⟩ := (P.lawValue_finite_C11 hw hc hH hbound h hh hb hm).2
  have hAC : AbsolutelyContinuousOnInterval g θ ρ := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := L)
    apply hLip.mono
    intro t ht
    have hq := hQuarter ht
    constructor <;> linarith [hq.1, hq.2]
  have hGlobal := (ae_restrict_iff' measurableSet_Ioo).mp
    (P.lawValue_secondDerivative_bound_ae hw hc hH hbound h hh hb hm)
  have hBound : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc θ ρ →
      ‖deriv g t‖ ≤ (8 * (w * H + c) + 6 * w ^ 2 * H * P.totalFirstMoment / c) * information P.law h := by
    filter_upwards [hGlobal, volume.ae_ne (-(1 / 4) : ℝ), volume.ae_ne (1 / 4 : ℝ)] with t ht hL hR
    intro htu
    have hq := hQuarter (uIoc_subset_uIcc htu)
    have hi : t ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) :=
      ⟨lt_of_le_of_ne hq.1 (Ne.symm hL), lt_of_le_of_ne hq.2 hR⟩
    simpa only [Real.norm_eq_abs] using ht hi
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const_ae hBound
  rw [hAC.integral_deriv_eq_sub] at hI
  simpa only [Real.norm_eq_abs] using hI

/-- Explicit finite law `C^{1,1}` constant, independent of the instance size. -/
theorem Instance.lawValue_uniform_C11 (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    (∀ θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      DifferentiableAt ℝ (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ) ∧
      ∃ K : ℝ≥0, (K : ℝ) = (8 * (w * H + c) + 6 * w ^ 2 * H * P.totalFirstMoment / c) * information P.law h ∧
        LipschitzOnWith K (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c))
          (Icc (-(1 / 4) : ℝ) (1 / 4)) := by
  have hS := P.totalFirstMoment_nonnegative
  have hI := information_nonnegative P.law h
  refine ⟨fun θ hθ ↦ (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hw hc hH hbound h hh hb hm
    (show θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) by constructor <;> linarith [hθ.1, hθ.2])).differentiableAt,
    ⟨NNReal.mk _ (by positivity), rfl, ?_⟩⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro θ hθ ρ hρ
  simpa only [Real.dist_eq, NNReal.coe_mk] using P.lawValue_deriv_lipschitz_information hw hc hH hbound h hh hb hm hρ hθ

end ProphetSecretary.Model
