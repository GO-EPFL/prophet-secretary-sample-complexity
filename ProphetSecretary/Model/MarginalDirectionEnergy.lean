import ProphetSecretary.Model.MarginalEnergy
import ProphetSecretary.Analysis.SumIntegralCauchy
import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Directional energy without atom coordinates

Cauchy-Schwarz across the marginal integrals converts the premium second-moment
bound into a directional Fisher-information bound. This analytic step applies
to every square-integrable score direction, including tilted scores.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.marginalPremium_direction_energy (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (s : Fin n → ℝ → ℝ) (hs : ∀ i, MemLp (s i) 2 (P.law i)) :
    (∑ i : Fin n, ∫ a, s i a * P.marginalPremium hP hw hc i a ∂P.law i) ^ 2 ≤
      2 * w ^ 2 * H * (P.valuePolicy hP hw.le hc).expectedDuration P *
        (P.valuePolicy hP hw.le hc).expectedReward P * ProphetSecretary.Probability.information P.law s := by
  have hCS := ProphetSecretary.Analysis.sum_integral_mul_sq_le P.law s (P.marginalPremium hP hw hc)
    hs (P.marginalPremium_memLp_two hP hw hc hH hbound)
  change _ ≤ ProphetSecretary.Probability.information P.law s *
    (∑ i : Fin n, ∫ a, (P.marginalPremium hP hw hc i a) ^ 2 ∂P.law i) at hCS
  have hE := mul_le_mul_of_nonneg_left (P.marginalPremium_secondMoment_le hP hw hc hH hbound)
    (ProphetSecretary.Probability.information_nonnegative P.law s)
  apply hCS.trans
  convert hE using 1
  ring

end ProphetSecretary.Model
