import ProphetSecretary.Stability.LawUniformRegularity
import ProphetSecretary.Analysis.LawCurvatureConstant

/-! # Uniformity over normalized scalar weights
The explicit constant is selected using only the offer cap and the compact
interior weight interval. Instance size and individual marginal probabilities
do not enter it.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n : ℕ}

theorem Instance.lawScalarUnit_deriv_lipschitz_uniform (P : Instance n) {H δ lam : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1 - δ))
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) (hρ : ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    |deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) lam (1 - lam)) ρ -
      deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) lam (1 - lam)) θ| ≤
      (lawCurvatureConstant H δ * (1 + P.totalFirstMoment) * information P.law h) * |ρ - θ| := by
  have hw : 0 < lam := hδ.trans_le hlam.1
  have hc : 0 < 1 - lam := by linarith [hlam.2]
  have hCoef := lawCurvatureCoefficient_le hH hδ hw.le (by linarith [hlam.2]) hc
    (by linarith) (by linarith [hlam.2]) P.totalFirstMoment_nonnegative
  have hI := information_nonnegative P.law h
  exact (P.lawValue_deriv_lipschitz_information hw hc hH hbound h hh hb hm hθ hρ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoef hI) (abs_nonneg _))

end ProphetSecretary.Model
