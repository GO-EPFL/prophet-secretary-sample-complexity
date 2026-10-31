import ProphetSecretary.Model.ScalarUniformRegularity
import ProphetSecretary.Analysis.PointwiseDerivativeRegularity

/-!
# Universal scalar curvature

This collects `thm:scalar-curvature` and
`eq:ps-universal-scalar-curvature`. The finite statements hold for integrable
expected maxima, hence in particular for bounded finite instances. The local
Lipschitz constants do not depend on the offer cap, laws, or instance size.
The pointwise-limit statement proves derivative convergence using the common
curvature bound rather than inferring it from value convergence alone.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

/-- `thm:scalar-curvature`, finite-instance statement, including the sharp a.e.
bound and the dimension-independent local C^{1,1} assertion. -/
theorem Instance.scalar_curvature {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    (∀ lam ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (fun z => optimalScalarValue P z (1 - z)) lam) ∧
      (∀ a b, 0 < a → b < 1 → LipschitzOnWith
        (Real.toNNReal (1 / (a ^ 2 * (1 - b))))
        (deriv (fun z => optimalScalarValue P z (1 - z))) (Icc a b)) ∧
      (∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1),
        0 ≤ deriv (deriv (fun z => optimalScalarValue P z (1 - z))) lam ∧
          deriv (deriv (fun z => optimalScalarValue P z (1 - z))) lam ≤
            1 / (lam ^ 2 * (1 - lam))) := by
  have h := P.scalarUnit_uniform_C11 hP
  refine ⟨h.1, ?_, P.scalarCurvature_ae hP⟩
  intro a b ha hb
  have hnonneg : 0 ≤ 1 / (a ^ 2 * (1 - b)) := by positivity
  simpa only [Real.toNNReal_of_nonneg hnonneg] using h.2 a b ha hb

/-- The pointwise-limit clause of `thm:scalar-curvature`. Every limit value is
real and finite. Instance sizes may vary without bound. Derivative convergence
is a consequence of the uniform estimates and is part of the conclusion. -/
theorem finite_scalar_pointwise_limit_C11 (n : ℕ → ℕ) (P : ∀ m, Instance (n m))
    (hP : ∀ m, Integrable Instance.maximum (P m).valuesLaw) (F : ℝ → ℝ)
    (hlimit : ∀ lam ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun m => optimalScalarValue (P m) lam (1 - lam)) atTop (𝓝 (F lam))) :
    (∀ lam ∈ Ioo (0 : ℝ) 1, HasDerivAt F (deriv F lam) lam) ∧
      (∀ lam ∈ Ioo (0 : ℝ) 1,
        Tendsto (fun m => deriv (fun z => optimalScalarValue (P m) z (1 - z)) lam)
          atTop (𝓝 (deriv F lam))) ∧
      (∀ a b, 0 < a → b < 1 → LipschitzOnWith
        (Real.toNNReal (1 / (a ^ 2 * (1 - b)))) (deriv F) (Icc a b)) := by
  apply ProphetSecretary.Analysis.pointwise_limit_local_C11
    (fun m z => optimalScalarValue (P m) z (1 - z))
    (fun m => deriv (fun z => optimalScalarValue (P m) z (1 - z))) F
    (fun a b => Real.toNNReal (1 / (a ^ 2 * (1 - b))))
  · intro m lam hlam
    exact ((P m).scalarUnit_hasDerivAt (hP m) hlam).differentiableAt.hasDerivAt
  · intro m a b ha hb
    exact ((P m).scalar_curvature (hP m)).2.1 a b ha hb
  · exact hlimit

end ProphetSecretary.Model
