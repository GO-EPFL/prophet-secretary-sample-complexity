import ProphetSecretary.Model.MarginalAffine
import ProphetSecretary.Model.MarginalDirectionEnergy

/-!
# The actual likelihood envelope gradient and its energy

Paper correspondence: `upfish:gradient` and `upfish:energy`. The centered
marginal acceptance premia represent the derivative of the reoptimized scalar
value, proved by exact marginal residuals and the fixed-policy envelope theorem.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.canonicalScore_derivative_eq_marginalPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    (P.valuePolicy hP hw.le hc).scalarLikelihoodDerivative P w c h =
      ∑ i : Fin n, ∫ a, h i a * P.marginalPremium hP hw hc i a ∂P.law i := by
  let C := P.valuePolicy hP hw.le hc
  have hInt (i : Fin n) : Integrable (fun ω : C.World ↦
      (w * C.realizedReward ω + c * C.realizedDuration ω) * h i (ω.1 i)) (P.worldLaw C.seedLaw) := by
    have hI := C.integrable_scalarScore_of_bounded P hH hbound hw.le hc (singleScore i (h i))
      (singleScore_measurable i (hh i)) (singleScore_bound P.law i (hb i))
    simpa only [singleScore_complete] using hI
  have he : (fun ω : C.World ↦ (w * C.realizedReward ω + c * C.realizedDuration ω) * completeScore h ω.1) =
      (fun ω ↦ ∑ i : Fin n, (w * C.realizedReward ω + c * C.realizedDuration ω) * h i (ω.1 i)) := by
    funext ω
    exact Finset.mul_sum _ _ _
  change (∫ ω : C.World, (w * C.realizedReward ω + c * C.realizedDuration ω) * completeScore h ω.1
    ∂P.worldLaw C.seedLaw) = _
  rw [he, integral_finsetSum Finset.univ (fun i _ ↦ hInt i)]
  apply Finset.sum_congr rfl
  intro i _
  have hSingle := P.canonical_singleScore_derivative hP hw hc hH hbound i (h i) (hh i) (hb i) (hm i)
  simpa only [RandomizedPolicy.scalarLikelihoodDerivative, singleScore_complete] using hSingle

/-- The optimized derivative is represented by the actual marginal premium
pairings. The base policy is fixed before taking the derivative. -/
theorem Instance.hasDerivAt_optimalScalarValue_marginalPremium (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H)
    (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    HasDerivAt (fun θ ↦ optimalScalarValue (P.likelihoodPath h hh hb hm θ) w c)
      (∑ i : Fin n, ∫ a, h i a * P.marginalPremium (P.integrable_maximum_of_bounded hbound) hw hc.le i a ∂P.law i) 0 := by
  have hD := P.hasDerivAt_optimalScalarValue_likelihoodPath hH hbound hw hc h hh hb hm
  rw [P.canonicalScore_derivative_eq_marginalPremium (P.integrable_maximum_of_bounded hbound)
    hw hc.le hH hbound h hh hb hm] at hD
  exact hD

/-- Directional version of `upfish:energy`, stated directly for the actual
optimized derivative and Fisher information, without atom coordinates. -/
theorem Instance.optimalScalarValue_likelihood_gradient_energy (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H)
    (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    (deriv (fun θ ↦ optimalScalarValue (P.likelihoodPath h hh hb hm θ) w c) 0) ^ 2 ≤
      2 * w ^ 2 * H * (P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc.le).expectedDuration P *
        (P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc.le).expectedReward P * information P.law h := by
  rw [(P.hasDerivAt_optimalScalarValue_marginalPremium hw hc hH hbound h hh hb hm).deriv]
  apply P.marginalPremium_direction_energy (P.integrable_maximum_of_bounded hbound) hw hc.le hH hbound h
  intro i
  exact MemLp.of_bound (hh i).aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb i)

end ProphetSecretary.Model
