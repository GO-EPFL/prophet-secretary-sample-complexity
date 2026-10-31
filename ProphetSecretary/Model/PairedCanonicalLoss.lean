import ProphetSecretary.Model.BellmanPerformance
import ProphetSecretary.Model.BellmanResidualBasic
import ProphetSecretary.Model.MarginalPremium
import ProphetSecretary.Analysis.PairedDecisionLoss

/-!
# Both canonical performance losses from the same value error

The design policy uses its own threshold and is assessed under another law.
The two directions of the performance identity share the TRUE-gap support
band, including exact threshold ties. This is the actual-policy bridge used
before the selected-weight and fixed-weight optimism integrations.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.valuePolicy_action_eq_gapDecision (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z : ℝ} (hz : 0≤z)
    (x u : Fin n → ℝ) (i : Fin n) :
    (Q.valuePolicy hQ zero_le_one hz).rule.action () Finset.univ x u i =
      decide (0 ≤ x i-Q.continuationAtArrival 1 z x u i) := by
  change decide (Q.valueThreshold 1 z (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i) = _
  rw [Q.continuationAtArrival_eq_threshold zero_lt_one z x u i,one_mul]
  simp only [sub_nonneg]

lemma Instance.valuePolicy_arrivalLoss_eq_gapLoss (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z : ℝ} (hz : 0≤z)
    (x u : Fin n → ℝ) (i : Fin n) :
    (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss P 1 z () x u i =
      ProphetSecretary.Analysis.gapLoss (decide (0≤x i-Q.continuationAtArrival 1 z x u i))
        (x i-P.continuationAtArrival 1 z x u i) := by
  unfold Policy.arrivalBellmanLoss
  simp only [one_mul]
  rw [← ProphetSecretary.Analysis.gapLoss_eq_decisionLoss]
  rw [Q.valuePolicy_action_eq_gapDecision hQ hz x u i]

/-- For canonical policies, the potential loss uses the candidate's value and
all clock/identity observations, but no other realized values. -/
lemma Instance.valuePolicy_arrivalLoss_values_invariant (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z : ℝ} (hz : 0≤z)
    (x y u : Fin n → ℝ) (i : Fin n) (hxi : x i=y i) :
    (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss P 1 z () x u i =
      (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss P 1 z () y u i := by
  rw [Q.valuePolicy_arrivalLoss_eq_gapLoss P hQ hz x u i,
    Q.valuePolicy_arrivalLoss_eq_gapLoss P hQ hz y u i,
    Q.continuationAtArrival_values_invariant 1 z x y u i,
    P.continuationAtArrival_values_invariant 1 z x y u i,hxi]

/-- Both actual Bellman losses are bounded by one error envelope supported on
the true continuation gap; the scalar z is fixed throughout this comparison. -/
theorem Instance.paired_canonical_arrivalLoss_bound (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {z E : ℝ} (hz : 0≤z) (x u : Fin n → ℝ) (i : Fin n)
    (hError : |P.continuationAtArrival 1 z x u i-Q.continuationAtArrival 1 z x u i| ≤ E) :
    (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss P 1 z () x u i ≤
        (if |x i-P.continuationAtArrival 1 z x u i| ≤ E then E else 0) ∧
      (P.valuePolicy hP zero_le_one hz).rule.arrivalBellmanLoss Q 1 z () x u i ≤
        (if |x i-P.continuationAtArrival 1 z x u i| ≤ E then E else 0) := by
  rw [Q.valuePolicy_arrivalLoss_eq_gapLoss P hQ hz x u i,
    P.valuePolicy_arrivalLoss_eq_gapLoss Q hP hz x u i]
  have hgap : |(x i-P.continuationAtArrival 1 z x u i)-(x i-Q.continuationAtArrival 1 z x u i)| ≤ E := by
    have heq : (x i-P.continuationAtArrival 1 z x u i)-(x i-Q.continuationAtArrival 1 z x u i) =
        Q.continuationAtArrival 1 z x u i-P.continuationAtArrival 1 z x u i := by ring
    rw [heq,abs_sub_comm]
    exact hError
  exact ProphetSecretary.Analysis.paired_gapLoss_bound hgap

end ProphetSecretary.Model
