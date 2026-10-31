import ProphetSecretary.Statistics.ReverseCandidateContribution
import ProphetSecretary.Statistics.CanonicalRegretCandidateBound

/-!
# Reverse performance difference reduces to empirical candidate contributions

The true canonical policy is evaluated under the empirical instance. Dropping
its empirical reach is legitimate because each Bellman action loss is
nonnegative. Finite-sum integration and the actual other-clock projection give
the explicit own-row contribution used in the fixed-scalar optimism argument.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma integrable_reverseTimeAverage (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi)
    (i : Fin n) (a : (Fin n × Fin k) → ℝ) (ha : ∀ j l, a (j,l)≤1) (x : ℝ) :
    Integrable (fun v => ∫ t,
      trueClockGapLossEmpiricalEval (P.restrictTo (Finset.univ.erase i))
        (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a)) z v x t
        ∂Instance.uniformClock) (Instance.clocksLaw (Finset.univ.erase i).card) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let y := reservoirCoordinates.symm (restrictTrainingCoordinates A a)
  have hm : Measurable (fun q : (Fin A.card → ℝ) × ℝ =>
      trueClockGapLossEmpiricalEval (P.restrictTo A) y z q.1 x q.2) :=
    measurable_trueClockGapLossEmpiricalEval (P.restrictTo A)
      (P.restrictTo_integrable_maximum A (P.integrable_maximum_of_bounded hbound))
      (fun _ _ => measurable_const) measurable_const measurable_snd measurable_const
      (fun j => (measurable_pi_apply j).comp measurable_fst) (fun _ => hz)
  apply Integrable.of_bound (hm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable (2+2*hi)
  exact Eventually.of_forall fun v => by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=Instance.uniformClock)
      (f:=fun t => trueClockGapLossEmpiricalEval (P.restrictTo A) y z v x t) (C:=2+2*hi) (by
        filter_upwards [uniformClock_nonnegative_ae] with t ht
        rw [Real.norm_eq_abs,abs_of_nonneg (trueClockGapLossEmpiricalEval_nonnegative _ _ _ _ _ _)]
        exact (paired_clockGapLoss_bounded (P.restrictTo A) (fun j => hbound (stateEmbedding A j))
          y (fun j l => ha (stateEmbedding A j) l) hz hzhi ht v x).2)

lemma reverse_candidateMean_integral_eq_contribution (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi)
    (i : Fin n) (a : (Fin n × Fin k) → ℝ) (ha : ∀ j l, a (j,l)≤1) :
    (∫ u, candidateLossMean P (totalEmpiricalInstance (reservoirCoordinates.symm a))
      (P.integrable_maximum_of_bounded hbound) z hz i u ∂Instance.clocksLaw n) =
      reverseCandidateContribution P z i a := by
  rw [(empirical_reverse_candidateMean_integral_otherClocks P (P.integrable_maximum_of_bounded hbound) a hz i).2]
  unfold empiricalReverseOtherCandidateLossMean reverseCandidateContribution
  rw [integral_const_mul,integral_finsetSum _ (fun l _ => integrable_reverseTimeAverage P hbound hz hzhi i a ha _)]

/-- The reverse empirical regret is bounded by the full sum of actual candidate
contributions on the common bounded-sample event. -/
theorem trueCanonical_empirical_regret_le_candidates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi)
    (a : (Fin n × Fin k) → ℝ) (ha : ∀ j l, a (j,l)≤1) :
    optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z-
      (P.valuePolicy (P.integrable_maximum_of_bounded hbound) zero_le_one hz).scalarObjective
        (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ≤
      ∑ i : Fin n, reverseCandidateContribution P z i a := by
  apply (P.canonical_regret_le_sum_candidateLossMean _ (P.integrable_maximum_of_bounded hbound)
    (totalEmpiricalInstance_integrable _) hz).trans_eq
  exact Finset.sum_congr rfl fun i _ => reverse_candidateMean_integral_eq_contribution P hbound hz hzhi i a ha

end ProphetSecretary.Model
