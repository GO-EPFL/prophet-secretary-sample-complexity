import ProphetSecretary.Reach.MarkovStrict

/-!
# Strict finite reach--duration comparison

This is equation `upbound:strict-reach` in `lem:monotone-reach` = `lem:strict-reach`.
The policy may use an arbitrary independent seed. The statement applies to every
measurable Markov threshold rule monotone in the unseen set, including rules
evaluated under laws different from those used to choose their thresholds.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem thresholdPolicy.strict_reach
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (hθ : MonotoneThresholds θ) (hπ : (thresholdPolicy θ).IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (thresholdPolicy θ).reachProbability P ν i - (thresholdPolicy θ).meanDuration P ν ≥
      ((thresholdPolicy θ).selectionProbability P ν i) ^ 2 / 2 := by
  exact markovPolicy.strict_reach (fun r A t i x => decide (θ r A t i ≤ x))
    (realThreshold_deletionMonotone θ hθ) hπ P ν i

/-- In particular, monotone Markov thresholds reach every variable with
probability at least their expected stopping time. -/
theorem thresholdPolicy.meanDuration_le_reachProbability
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (hθ : MonotoneThresholds θ) (hπ : (thresholdPolicy θ).IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (thresholdPolicy θ).meanDuration P ν ≤ (thresholdPolicy θ).reachProbability P ν i := by
  have h := thresholdPolicy.strict_reach θ hθ hπ P ν i
  nlinarith [sq_nonneg ((thresholdPolicy θ).selectionProbability P ν i)]

end ProphetSecretary.Model
