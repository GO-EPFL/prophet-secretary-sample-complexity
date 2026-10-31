import ProphetSecretary.Statistics.MixedEmpiricalSlopeFunctions
import ProphetSecretary.Statistics.BoundedFreshStep

/-!
# Fresh scalar-increment moments with known laws

Normalized mixed jump differences vanish identically at known marginals.
Unknown marginals use the actual bounded premium-difference function at their
future-dependent mixed continuations. Both scalar weights are fixed while
fresh-sample conditional centering and moments are taken.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedJumpSlope_unknown_eq_centeredFreshStep (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n) (hi : i∉known)
    (a : (Fin n × Fin k) → ℝ) (x : ℝ) :
    (P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z u i a) x -
      P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z' u i a) x) / (z' - z) =
      ProphetSecretary.Statistics.centeredFreshStep (P.law i) k (mixedOfferSlope P known z z' u i) (a, x) := by
  simp only [Instance.mixedPremiumJump,if_neg hi]
  rw [ProphetSecretary.Statistics.centeredFreshStep, integral_mixedOfferSlope P hP known z z' u i a]
  change ((k : ℝ)⁻¹ * (max (max 0 x - mixedArrivalContinuation P known 1 z u i a) 0 -
      positivePremium (P.law i) 1 (mixedArrivalContinuation P known 1 z u i a)) -
    (k : ℝ)⁻¹ * (max (max 0 x - mixedArrivalContinuation P known 1 z' u i a) 0 -
      positivePremium (P.law i) 1 (mixedArrivalContinuation P known 1 z' u i a))) / (z' - z) =
    (k : ℝ)⁻¹ * ((max (max 0 x - mixedArrivalContinuation P known 1 z u i a) 0 -
      max (max 0 x - mixedArrivalContinuation P known 1 z' u i a) 0) / (z' - z) -
      (positivePremium (P.law i) 1 (mixedArrivalContinuation P known 1 z u i a) -
      positivePremium (P.law i) 1 (mixedArrivalContinuation P known 1 z' u i a)) / (z' - z))
  ring

/-- Fresh-coordinate conditional moments of the normalized actual reverse-jump
increment. Both scalars are fixed, while all earlier revealed samples remain random. -/
theorem Instance.canonicalMixedSlopeFreshJump_conditional_moments (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (i : Fin n) (j : Fin k)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (hui : 0 ≤ u i)
    (s : Finset (Fin n × Fin k)) (hfresh : (i, j) ∉ s)
    (hfuture : ∀ q∈futureSampleRows u i, q∉known → ∀ a : Fin k, (q,a)∈s) :
    let ρ := P.trainingCoordinateLaw k
    let d := fun a : (Fin n × Fin k) → ℝ =>
      (P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z u i a) (a (i, j)) -
        P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z' u i a) (a (i, j))) / (z' - z)
    let p := fun a => if i∈known then 0 else (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i
    let info := ProphetSecretary.Probability.revealedCoordinateSigma s
    ρ[d | info] =ᵐ[ρ] 0 ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 2) | info]) a ≤ p a / (k : ℝ) ^ 2) ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 6) | info]) a ≤ p a / (k : ℝ) ^ 6) := by
  by_cases hi : i∈known
  · simp [Instance.mixedPremiumJump,hi]
    exact Filter.Eventually.of_forall fun _ => rfl
  · have h := P.boundedFreshStep_conditional_moments (i, j) s hfresh
      (measurable_mixedOfferSlope P hP known hz (hz.trans hzz.le) u i)
      (mixedOfferSlope_bounds P hP known hz hzz u i hui)
      (mixedOfferSlope_mask P known z z' u i s hfuture)
    have heq (a : (Fin n × Fin k) → ℝ) :
        ProphetSecretary.Statistics.centeredFreshStep (P.law i) k (mixedOfferSlope P known z z' u i) (a, a (i, j)) =
        (P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z u i a) (a (i, j)) -
          P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z' u i a) (a (i, j))) / (z' - z) :=
      (mixedJumpSlope_unknown_eq_centeredFreshStep P hP known z z' u i hi a (a (i, j))).symm
    simpa only [heq, integral_mixedOfferSlope P hP known,if_neg hi] using h

end ProphetSecretary.Model
