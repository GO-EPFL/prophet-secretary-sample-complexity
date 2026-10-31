import ProphetSecretary.Statistics.CanonicalCandidateLoss

/-!
# Canonical regret bounded by candidate value/clock integrals

The general-policy performance difference drops nonnegative reach indicators.
The actual independent candidate replacement identity then integrates each
potential canonical loss against its marginal offer law and uniform arrival
time, keeping the scalar coefficient fixed.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.canonical_regret_le_sum_candidateLossMean (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {z : ℝ} (hz : 0≤z) :
    optimalScalarValue P 1 z-(Q.valuePolicy hQ zero_le_one hz).scalarObjective P 1 z ≤
      ∑ i, ∫ u, candidateLossMean Q P hQ z hz i u ∂Instance.clocksLaw n := by
  let π := Q.valuePolicy hQ zero_le_one hz
  let rule : Policy Unit n := π.rule
  have hd := π.scalarRegret_le_sum_arrivalLoss P hP zero_lt_one hz
  change optimalScalarValue P 1 z-π.scalarObjective P 1 z ≤
    ∑ i, ∫ ω : World n Unit, rule.arrivalBellmanLoss P 1 z ω.2.2 ω.1 ω.2.1 i
      ∂P.worldLaw (Measure.dirac ()) at hd
  apply hd.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  have hUnit : (∫ ω : World n Unit, rule.arrivalBellmanLoss P 1 z ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ())) =
      ∫ ω : World n Unit, rule.arrivalBellmanLoss P 1 z () ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ()) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by rcases ω with ⟨x,u,r⟩; cases r; rfl
  exact hUnit.trans (canonical_arrivalLoss_candidate_integral Q P hQ hP z hz i).2

end ProphetSecretary.Model
