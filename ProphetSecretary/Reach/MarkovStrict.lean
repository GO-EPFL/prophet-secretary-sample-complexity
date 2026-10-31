import ProphetSecretary.Reach.StrictComparison
import ProphetSecretary.Model.MarkovAcceptance

/-!
# Strict reach for deletion-monotone Markov rules

This proves equation `upbound:strict-reach` for the complete Markov acceptance class,
including extended thresholds `+∞` and `−∞`. The pending comparison is derived from
history projection and deletion monotonicity on the valid observation domain.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem markovPolicy.strict_reach
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool)
    (ha : DeletionMonotoneAcceptance accept) (hπ : (markovPolicy accept).IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (markovPolicy accept).reachProbability P ν i - (markovPolicy accept).meanDuration P ν ≥
      ((markovPolicy accept).selectionProbability P ν i) ^ 2 / 2 := by
  apply (markovPolicy accept).strict_reach_of_pending_domination hπ P ν i
  intro r x u hx hu
  exact markovPolicy.stoppingTime_le_pendingTime accept ha r x u hx hu i

theorem markovPolicy.meanDuration_le_reachProbability
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool)
    (ha : DeletionMonotoneAcceptance accept) (hπ : (markovPolicy accept).IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (markovPolicy accept).meanDuration P ν ≤ (markovPolicy accept).reachProbability P ν i := by
  have h := markovPolicy.strict_reach accept ha hπ P ν i
  nlinarith [sq_nonneg ((markovPolicy accept).selectionProbability P ν i)]

theorem extendedThresholdPolicy.strict_reach
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal)
    (hθ : MonotoneExtendedThresholds θ) (hπ : (extendedThresholdPolicy θ).IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (extendedThresholdPolicy θ).reachProbability P ν i - (extendedThresholdPolicy θ).meanDuration P ν ≥
      ((extendedThresholdPolicy θ).selectionProbability P ν i) ^ 2 / 2 :=
  markovPolicy.strict_reach _ (extendedThresholdPolicy.deletionMonotone θ hθ) hπ P ν i

theorem extendedThresholdPolicy.meanDuration_le_reachProbability
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal)
    (hθ : MonotoneExtendedThresholds θ) (hπ : (extendedThresholdPolicy θ).IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (extendedThresholdPolicy θ).meanDuration P ν ≤ (extendedThresholdPolicy θ).reachProbability P ν i :=
  markovPolicy.meanDuration_le_reachProbability _ (extendedThresholdPolicy.deletionMonotone θ hθ) hπ P ν i

end ProphetSecretary.Model
