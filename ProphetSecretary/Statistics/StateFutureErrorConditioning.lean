import ProphetSecretary.Statistics.StateFutureErrorBounds

/-!
# Localized conditional moments after a deterministic clock history

The CE is with respect to elapsed clocks only: training is still independent
and averaged. The actual restart identity and kernel law transfer localized
moments to every true critical prefix, without a supplied independence field.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.stateFutureError_condExp_moment_transfer (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a K : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (p : ℕ)
    (hkernel : ∀ u : Fin n → ℝ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi ≤ a →
      (∫ r, P.restartedFutureError k lo hi t u r ^ p
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤ K) :
    let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
    ∀ᵐ q ∂μ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a →
      μ[(fun r => P.stateFutureError k lo hi t r ^ p) |
        ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] q ≤ K := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hf := P.integrable_stateFutureError_pow (k := k) hbound lo hi ht0 ht1 p
  have hCE := ProphetSecretary.Probability.condExp_observedClockHistory (n := n)
    (P.trainingCoordinateLaw k) ht0 ht1 ((P.measurable_stateFutureError lo hi t).pow_const p) hf
  filter_upwards [hCE] with q hq
  intro hValue
  have hv : ∀ᵐ r ∂μ, ∀ i, 0 ≤ r.2 i :=
    (measurePreserving_snd (μ := P.trainingCoordinateLaw k) (ν := Instance.clocksLaw n)).quasiMeasurePreserving.ae
      ((Instance.clocks_mem_unitInterval (n := n)).mono fun _ h => fun i => (h i).1)
  have hEq : (∫ r, P.stateFutureError k lo hi t
      (ProphetSecretary.Probability.restartTrainingClocks t (q,r)) ^ p ∂μ) =
      ∫ r, P.restartedFutureError k lo hi t q.2 r ^ p ∂μ := by
    apply integral_congr_ae
    exact hv.mono fun r hr => congrArg (fun x : ℝ => x^p) (P.stateFutureError_restart lo hi ht1 q r hr)
  rw [hq, hEq]
  exact hkernel q.2 hValue

/-- The explicit second conditional moment used by finite-grid entrances. -/
theorem Instance.stateFutureError_condExp_secondMoment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
    ∀ᵐ q ∂μ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a →
      μ[(fun r => P.stateFutureError k lo hi t r ^ 2) |
        ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] q ≤
      (16 * (18 * (128 + 4 * (hi-lo)^2 / hi))) * (a / (k : ℝ) + 1 / (k : ℝ)^2) := by
  apply P.stateFutureError_condExp_moment_transfer hbound ht0 ht1 2
  intro u hValue
  exact (P.restartedFutureError_secondMoment (k := k) hbound hlo hlohi hhi ht0 ht1 u hValue).2

/-- The sixth conditional moment uses the same actual clock-history reset. -/
theorem Instance.stateFutureError_condExp_sixthMoment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
    ∀ᵐ q ∂μ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 hi ≤ a →
      μ[(fun r => P.stateFutureError k lo hi t r ^ 6) |
        ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n t] q ≤
      (832 * (23328 * (2 * (6672000000000 ^ 2 + 13348000000000) +
        (106000000000 ^ 2 + 212000000000) * (hi-lo)^6 / hi^3))) *
        (a^3 / (k : ℝ)^3 + 1 / (k : ℝ)^6) := by
  apply P.stateFutureError_condExp_moment_transfer hbound ht0 ht1 6
  intro u hValue
  exact (P.restartedFutureError_sixthMoment (k := k) hbound hlo hlohi hhi ht0 ht1 u hValue).2

end ProphetSecretary.Model
