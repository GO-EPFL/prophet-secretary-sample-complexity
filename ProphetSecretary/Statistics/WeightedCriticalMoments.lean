import ProphetSecretary.Statistics.ObservedCriticalPrefixes
import ProphetSecretary.Probability.ConditionalWeightBounds

/-!
# Observable weighted moments at true critical prefixes

The constants are explicit, depend only on the scalar interval and sample
budget, and are independent of the finite number of offers. Any bounded
nonnegative clock-history multiplier supported on the true critical region may
multiply the conditional moment estimate, as needed at grid entrances.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

noncomputable def empiricalRestartMomentBound (k : ℕ) (lo hi a : ℝ) (p : ℕ) : ℝ :=
  if p=2 then
    (16 * (18 * (128 + 4 * (hi-lo)^2 / hi))) * (a / (k : ℝ) + 1 / (k : ℝ)^2)
  else
    (832 * (23328 * (2 * (6672000000000 ^ 2 + 13348000000000) +
      (106000000000 ^ 2 + 212000000000) * (hi-lo)^6 / hi^3))) *
      (a^3 / (k : ℝ)^3 + 1 / (k : ℝ)^6)

variable {n k : ℕ} [NeZero k]

lemma Instance.stateFutureError_condExp_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
    ∀ᵐ q ∂μ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a →
      μ[(fun r => P.stateFutureError k lo hi t r ^ p) |
        ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] q ≤
      empiricalRestartMomentBound k lo hi a p := by
  rcases hp with rfl | rfl
  · exact P.stateFutureError_condExp_secondMoment hbound hlo hlohi hhi ht0 ht1
  · simpa only [empiricalRestartMomentBound, show ¬(6:ℕ)=2 by omega, ite_false] using
      P.stateFutureError_condExp_sixthMoment hbound hlo hlohi hhi ht0 ht1

/-- The random multiplier observes only elapsed clocks, and its support lies in
the actual true-law critical region. No training-selected centering is used. -/
theorem Instance.weighted_critical_stateFutureError_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a D : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {p : ℕ} (hp : p=2 ∨ p=6)
    (H : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ)
    (hH : StronglyMeasurable[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] H)
    (hD : 0 ≤ D)
    (hHb : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ H q ∧ H q ≤ D)
    (hcritical : ∀ q, H q ≠ 0 →
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a) :
    (∫ q, H q * P.stateFutureError k lo hi t q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * ∫ q, H q
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
  have hC := P.stateFutureError_condExp_moment (k := k) (a := a) hbound hlo hlohi hhi ht0 ht1 hp
  apply ProphetSecretary.Probability.integral_weighted_condExp_bound
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (ProphetSecretary.Probability.observedClockSigma_le t) hH
    (P.integrable_stateFutureError_pow hbound lo hi ht0 ht1 p) hD hHb
  exact hC.mono fun q hq hne => hq (hcritical q hne)

end ProphetSecretary.Model
