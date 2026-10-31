import ProphetSecretary.Model.BoundaryHessian
import ProphetSecretary.Model.NormalizedRegret
import ProphetSecretary.Analysis.NormalizedQuotient

/-!
# Finite scalar curvature at the optimal policy

The boundary Hessian equals the total crossing selection charge times the
explicit normalization factor. Its expectation is at most one, independently
of the finite number of distributions.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.scalarBregman_limit_of_regular (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hr0 : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ (i : Fin n) (A : Finset (Fin n)),
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) ((1 - lam) / lam) (ω.1 i) ≠ 0) :
    let hz : 0 < (1 - lam) / lam := div_pos (sub_pos.mpr hlam.2) hlam.1
    Tendsto (fun h : ℝ ↦ (optimalScalarValue P (lam + h) (1 - (lam + h)) - optimalScalarValue P lam (1 - lam) -
      h * deriv (fun rho ↦ optimalScalarValue P rho (1 - rho)) lam) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (P.meanBoundaryCharge hP hz / (2 * lam ^ 2 * (1 - lam)))) := by
  let z := (1 - lam) / lam
  have hz : 0 < z := div_pos (sub_pos.mpr hlam.2) hlam.1
  have hd := P.durationRegret_limit hP hz hr0
  have hNorm := ProphetSecretary.Analysis.tendsto_normalized_duration_quotient hlam.1 hd
  have hCoeff : (P.meanBoundaryCharge hP hz / (2 * z)) / lam ^ 3 =
      P.meanBoundaryCharge hP hz / (2 * lam ^ 2 * (1 - lam)) := by
    dsimp only [z]
    field_simp [hlam.1.ne', (sub_pos.mpr hlam.2).ne']
  rw [hCoeff] at hNorm
  apply hNorm.congr'
  have hIn : ∀ᶠ h : ℝ in 𝓝 0, lam + h ∈ Ioo (0 : ℝ) 1 := by
    have hc : Continuous (fun h : ℝ ↦ lam + h) := continuous_const.add continuous_id
    exact (show Tendsto (fun h : ℝ ↦ lam + h) (𝓝 0) (𝓝 lam) by simpa only [add_zero] using hc.tendsto 0)
      (Ioo_mem_nhds hlam.1 hlam.2)
  filter_upwards [hIn.filter_mono nhdsWithin_le_nhds] with h hh
  have hratio : (1 - (lam + h)) / (lam + h) = z + -h / (lam * (lam + h)) := by
    dsimp only [z]
    field_simp [hlam.1.ne', hh.1.ne']
    ring
  have he := P.scalarBregman_eq_normalizedRegret hP hlam (lam + h)
  dsimp only at he
  rw [add_sub_cancel_left] at he
  rw [(P.scalarUnit_hasDerivAt hP hlam).deriv, he,
    P.normalizedRegret_eq_durationRegret hP hlam hh, hratio]

/-- The sharp finite-instance Hessian formula holds for almost every interior
weight, with no atomlessness assumption on the offer distributions. -/
theorem Instance.scalarHessian_formula_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1),
      ∃ hz : 0 < (1 - lam) / lam,
        DifferentiableAt ℝ (deriv (fun rho ↦ optimalScalarValue P rho (1 - rho))) lam ∧
        deriv (deriv (fun rho ↦ optimalScalarValue P rho (1 - rho))) lam =
          P.meanBoundaryCharge hP hz / (lam ^ 2 * (1 - lam)) := by
  let f : ℝ → ℝ := fun rho ↦ optimalScalarValue P rho (1 - rho)
  have hconv : ConvexOn ℝ (Ioo (0 : ℝ) 1) f :=
    (optimalScalarValue_weight_convex P hP).subset Ioo_subset_Icc_self (convex_Ioo _ _)
  have hf : ∀ lam ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ f lam :=
    fun lam hlam ↦ (P.scalarUnit_hasDerivAt hP hlam).differentiableAt
  filter_upwards [ProphetSecretary.Analysis.convex_ae_secondDerivative hconv hf,
    P.all_crossingTimes_ne_zero_ae hP (Measure.dirac ()), ae_restrict_mem measurableSet_Ioo] with lam hD hr hlam
  have hz : 0 < (1 - lam) / lam := div_pos (sub_pos.mpr hlam.2) hlam.1
  refine ⟨hz, hD, ?_⟩
  have hPeano := ProphetSecretary.Analysis.tendsto_bregman_quotient hlam
    (fun y hy ↦ (hf y hy).hasDerivAt) hD.hasDerivAt
  have hBoundary := P.scalarBregman_limit_of_regular hP hlam hr
  have he := tendsto_nhds_unique hPeano hBoundary
  change deriv (deriv f) lam / 2 = P.meanBoundaryCharge hP hz / (2 * lam ^ 2 * (1 - lam)) at he
  change deriv (deriv f) lam = _
  field_simp [hlam.1.ne', (sub_pos.mpr hlam.2).ne'] at he ⊢
  nlinarith [he]

/-- `thm:scalar-curvature`, finite-instance almost-everywhere differential
bound. The constant is independent of instance size. -/
theorem Instance.scalarCurvature_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ deriv (deriv (fun rho ↦ optimalScalarValue P rho (1 - rho))) lam ∧
        deriv (deriv (fun rho ↦ optimalScalarValue P rho (1 - rho))) lam ≤
          1 / (lam ^ 2 * (1 - lam)) := by
  filter_upwards [P.scalarHessian_formula_ae hP, ae_restrict_mem measurableSet_Ioo] with lam h hlam
  obtain ⟨hz, _hD, he⟩ := h
  rw [he]
  have hden : 0 < lam ^ 2 * (1 - lam) := mul_pos (sq_pos_of_pos hlam.1) (sub_pos.mpr hlam.2)
  exact ⟨div_nonneg (P.meanBoundaryCharge_nonnegative hP hz) hden.le,
    div_le_div_of_nonneg_right (P.meanBoundaryCharge_le_one hP hz) hden.le⟩

end ProphetSecretary.Model
