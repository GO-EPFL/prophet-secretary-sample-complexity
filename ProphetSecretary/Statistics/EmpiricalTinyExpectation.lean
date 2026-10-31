import ProphetSecretary.Statistics.EmpiricalPendingFirstMoment
import ProphetSecretary.Analysis.AveragedTinyLoss

/-!
# Tiny-offer expectations with the actual true and empirical pending means

The target of the Bellman loss determines which pending first moment appears.
Both means are computed under the actual independent training/clock law.
The local dominance and integrability hypotheses are elementary properties
of the concrete paired losses, supplied by the clock-loss and measurability
lemmas when this expectation estimate is instantiated.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

noncomputable def empiricalTinyRegretConstant (lo hi : ℝ) : ℝ := 1/lo + (2+hi)/lo^2

variable {n k : ℕ} [NeZero k]

noncomputable def Instance.tinyTargetPendingMean (P : Instance n) (targetEmpirical : Bool)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  if targetEmpirical then
    ((totalEmpiricalInstance (reservoirCoordinates.symm q.1)).restrictTo
      (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment
  else (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment

lemma Instance.tinyTargetPendingMean_integral (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (b : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun q => P.tinyTargetPendingMean (k := k) b q t)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, P.tinyTargetPendingMean (k := k) b q t
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = (1-t)*P.totalFirstMoment := by
  cases b
  · exact P.true_pendingFirstMoment_integral ht0 ht1
  · exact P.empirical_pendingFirstMoment_integral hP ht0 ht1

/-- A tiny-loss expectation estimate with all pending-mean assertions proved.
True loss uses targetEmpirical=false; empirical loss uses true. -/
theorem Instance.empirical_tiny_expectation_from_dom (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (b : Bool) {lo hi x : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hx : 0 ≤ x)
    {L : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ}
    (hI : Integrable L (((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).prod Instance.uniformClock))
    (hL0 : ∀ q t, 0 ≤ L (q,t))
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      L (q,t) ≤ (Icc (1-x/lo) 1).indicator
        (fun t => x+P.tinyTargetPendingMean (k := k) b q t+hi*(1-t)) t) :
    (∫ q, (∫ t, L (q,t) ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x^2 := by
  exact ProphetSecretary.Analysis.integral_averaged_tiny_loss_le
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) hI hL0 hlo hhi P.totalFirstMoment_nonnegative hx
    (fun t ht => (P.tinyTargetPendingMean_integral hP b ht.1 ht.2).1)
    (fun t ht => (P.tinyTargetPendingMean_integral hP b ht.1 ht.2).2.le) hdom

lemma Instance.empirical_tiny_expectation_rate_from_dom (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (b : Bool) {lo hi x : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hx : 0 ≤ x) (hxk : x ≤ 1 / (k : ℝ))
    {L : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ}
    (hI : Integrable L (((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).prod Instance.uniformClock))
    (hL0 : ∀ q t, 0 ≤ L (q,t))
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      L (q,t) ≤ (Icc (1-x/lo) 1).indicator
        (fun t => x+P.tinyTargetPendingMean (k := k) b q t+hi*(1-t)) t) :
    (∫ q, (∫ t, L (q,t) ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  have h := P.empirical_tiny_expectation_from_dom hP b hlo hhi hx hI hL0 hdom
  have hx2 : x^2 ≤ x/(k : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hxk hx
    simpa only [pow_two, mul_one_div] using hm
  have hC : 0 ≤ empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment) := by
    have hS := P.totalFirstMoment_nonnegative
    unfold empiricalTinyRegretConstant
    positivity
  exact h.trans ((mul_le_mul_of_nonneg_left hx2 hC).trans_eq (by ring))

end ProphetSecretary.Model
