import ProphetSecretary.Statistics.ObservedCriticalPrefixes
import ProphetSecretary.Statistics.MixedStateFutureErrorConditioning
import ProphetSecretary.Statistics.WeightedCriticalMoments
import ProphetSecretary.Probability.ConditionalWeightBounds

/-!
# Clock-observable weighted mixed error moments

The actual mixed conditional moment estimate may be multiplied by any bounded
nonnegative elapsed-clock observable supported in the true critical region.
The constant is the same explicit restart bound, independent of the number of
identities and known labels; no training-selected centering is used.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.mixedStateFutureError_condExp_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
    ∀ᵐ q ∂μ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a →
      μ[(fun r => P.mixedStateFutureError known k lo hi t r ^ p) |
        ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] q ≤
      empiricalRestartMomentBound k lo hi a p := by
  rcases hp with rfl | rfl
  · exact P.mixedStateFutureError_condExp_secondMoment known hbound hlo hlohi hhi ht0 ht1
  · simpa only [empiricalRestartMomentBound, show ¬(6:ℕ)=2 by omega, ite_false] using
      P.mixedStateFutureError_condExp_sixthMoment known hbound hlo hlohi hhi ht0 ht1

/-- The random multiplier observes only elapsed clocks, and its support lies in
the actual true-law critical region. No training-selected centering is used. -/
theorem Instance.weighted_critical_mixedStateFutureError_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a D : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {p : ℕ} (hp : p=2 ∨ p=6)
    (H : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ)
    (hH : StronglyMeasurable[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] H)
    (hD : 0 ≤ D)
    (hHb : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ H q ∧ H q ≤ D)
    (hcritical : ∀ q, H q ≠ 0 →
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a) :
    (∫ q, H q * P.mixedStateFutureError known k lo hi t q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * ∫ q, H q
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
  have hC := P.mixedStateFutureError_condExp_moment (k := k) (a := a) known hbound hlo hlohi hhi ht0 ht1 hp
  apply ProphetSecretary.Probability.integral_weighted_condExp_bound
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (ProphetSecretary.Probability.observedClockSigma_le t) hH
    (P.integrable_mixedStateFutureError_pow known hbound lo hi ht0 ht1 p) hD hHb
  exact hC.mono fun q hq hne => hq (hcritical q hne)

end ProphetSecretary.Model
