import ProphetSecretary.Statistics.EmpiricalSlopeFunctions
import ProphetSecretary.Statistics.BoundedFreshStep

/-!
# Conditional budgets for empirical scalar increments

The two design continuations are functions of the already revealed future rows.
Their normalized premium difference is evaluated on the next independent sample.
The resulting actual conditional second and sixth moments retain the true-law
premium difference as their budget.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma empiricalJumpSlope_eq_centeredFreshStep (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (a : (Fin n × Fin k) → ℝ) (x : ℝ) :
    (P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z u i a) x -
      P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z' u i a) x) / (z' - z) =
      ProphetSecretary.Statistics.centeredFreshStep (P.law i) k (empiricalOfferSlope z z' u i) (a, x) := by
  rw [ProphetSecretary.Statistics.centeredFreshStep, integral_empiricalOfferSlope P hP z z' u i a]
  change ((k : ℝ)⁻¹ * (max (max 0 x - empiricalArrivalContinuation 1 z u i a) 0 -
      positivePremium (P.law i) 1 (empiricalArrivalContinuation 1 z u i a)) -
    (k : ℝ)⁻¹ * (max (max 0 x - empiricalArrivalContinuation 1 z' u i a) 0 -
      positivePremium (P.law i) 1 (empiricalArrivalContinuation 1 z' u i a))) / (z' - z) =
    (k : ℝ)⁻¹ * ((max (max 0 x - empiricalArrivalContinuation 1 z u i a) 0 -
      max (max 0 x - empiricalArrivalContinuation 1 z' u i a) 0) / (z' - z) -
      (positivePremium (P.law i) 1 (empiricalArrivalContinuation 1 z u i a) -
      positivePremium (P.law i) 1 (empiricalArrivalContinuation 1 z' u i a)) / (z' - z))
  ring

/-- Fresh-coordinate conditional moments of the normalized actual reverse-jump
increment. Both scalars are fixed, while all earlier revealed samples remain random. -/
theorem Instance.canonicalEmpiricalSlopeFreshJump_conditional_moments (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) (j : Fin k)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (hui : 0 ≤ u i)
    (s : Finset (Fin n × Fin k)) (hfresh : (i, j) ∉ s)
    (hfuture : ∀ q ∈ futureSampleRows u i, ∀ a : Fin k, (q, a) ∈ s) :
    let ρ := P.trainingCoordinateLaw k
    let d := fun a : (Fin n × Fin k) → ℝ =>
      (P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z u i a) (a (i, j)) -
        P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z' u i a) (a (i, j))) / (z' - z)
    let p := fun a => (totalEmpiricalInstance (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i
    let info := ProphetSecretary.Probability.revealedCoordinateSigma s
    ρ[d | info] =ᵐ[ρ] 0 ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 2) | info]) a ≤ p a / (k : ℝ) ^ 2) ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 6) | info]) a ≤ p a / (k : ℝ) ^ 6) := by
  have h := P.boundedFreshStep_conditional_moments (i, j) s hfresh
    (measurable_empiricalOfferSlope hz (hz.trans hzz.le) u i)
    (empiricalOfferSlope_bounds hz hzz u i hui)
    (empiricalOfferSlope_mask z z' u i s hfuture)
  have heq (a : (Fin n × Fin k) → ℝ) :
      ProphetSecretary.Statistics.centeredFreshStep (P.law i) k (empiricalOfferSlope z z' u i) (a, a (i, j)) =
      (P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z u i a) (a (i, j)) -
        P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z' u i a) (a (i, j))) / (z' - z) :=
    (empiricalJumpSlope_eq_centeredFreshStep P hP z z' u i a (a (i, j))).symm
  simpa only [heq, integral_empiricalOfferSlope P hP] using h

end ProphetSecretary.Model
