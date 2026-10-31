import ProphetSecretary.Model.ScalarUniformRegularity
import ProphetSecretary.Analysis.SmoothSupport

/-!
# Integrated uniform scalar curvature

Paper correspondence: the integrated form of `thm:scalar-curvature`. The
constant depends only on the displayed interior interval, never on instance
size or the offer laws.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.scalarUnit_quadraticGap_uniform (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a b lam rho : ℝ}
    (ha : 0 < a) (hb : b < 1) (hlam : lam ∈ Icc a b) (hrho : rho ∈ Icc a b) :
    let gap := optimalScalarValue P rho (1 - rho) - optimalScalarValue P lam (1 - lam) -
      (rho - lam) * deriv (fun z ↦ optimalScalarValue P z (1 - z)) lam
    0 ≤ gap ∧ gap ≤ (1 / (a ^ 2 * (1 - b))) * (rho - lam) ^ 2 / 2 := by
  have hconv : ConvexOn ℝ (Icc a b) (fun z ↦ optimalScalarValue P z (1 - z)) :=
    (optimalScalarValue_weight_convex P hP).subset
      (fun z hz ↦ ⟨(ha.trans_le hz.1).le, (hz.2.trans_lt hb).le⟩) (convex_Icc _ _)
  apply ProphetSecretary.Analysis.quadratic_support_of_deriv_lipschitz hconv
    (fun z hz ↦ (P.scalarUnit_hasDerivAt hP ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩).differentiableAt.hasDerivAt)
    (fun x hx y hy ↦ P.scalarUnit_deriv_lipschitz_uniform hP ha hb hx hy) hlam hrho

end ProphetSecretary.Model
