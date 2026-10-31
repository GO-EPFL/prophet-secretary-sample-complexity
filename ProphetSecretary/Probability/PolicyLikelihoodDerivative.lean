import ProphetSecretary.Stability.LikelihoodEnvelope
import ProphetSecretary.Analysis.QuadraticSupport

/-!
# Differentiating a fixed online payoff

The policy is fixed at the base law. The complete-vector score includes all
coordinates, even those arriving after stopping, and remains analytical only.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem RandomizedPolicy.hasDerivAt_scalarObjective_likelihoodPath (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    HasDerivAt (fun θ ↦ π.scalarObjective (P.likelihoodPath h hh hb hm θ) w c)
      (π.scalarLikelihoodDerivative P w c h) 0 := by
  apply ProphetSecretary.Analysis.hasDerivAt_of_quadratic_remainder
    (K := 2 * (w * H + c) * ProphetSecretary.Probability.information P.law h)
  filter_upwards [Icc_mem_nhds (by norm_num : -(1 / 4 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 4)] with θ hθ
  have hθ' : |θ| ≤ 1 / 4 := abs_le.mpr hθ
  rw [P.likelihoodPath_of_mem h hh hb hm hθ', P.likelihoodPath_zero h hh hb hm]
  simp only [sub_zero]
  have ht := π.scalarObjective_likelihood_taylor P hH hbound hw hc h hh hb hm hθ'
  change |π.scalarObjective (P.likelihoodTilt h hh hb hm θ hθ') w c - π.scalarObjective P w c -
    θ * π.scalarLikelihoodDerivative P w c h| ≤ _ at ht
  convert ht using 1
  ring

end ProphetSecretary.Model
