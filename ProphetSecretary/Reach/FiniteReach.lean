import ProphetSecretary.Reach.Pending
import ProphetSecretary.Reach.IndependentReachBounds
import ProphetSecretary.Model.Outcome

/-!
# Finite-instance reach and duration

Paper correspondence: `lem:monotone-reach` = `lem:strict-reach`.
The reach event is defined from the executed online policy. The auxiliary pending
execution and its independence are supplied by the preceding construction and proofs.
-/

open MeasureTheory Set ProbabilityTheory

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- The manuscript's `qᵢ`, including all independent auxiliary randomness. -/
noncomputable def Policy.reachProbability (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (i : Fin n) : ℝ :=
  (P.worldLaw ν).real {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i}

/-- The probability of selecting a particular identity. Ties use deterministic identity order. -/
noncomputable def Policy.selectionProbability (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (i : Fin n) : ℝ :=
  (P.worldLaw ν).real {ω : World n Seed | π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i}

noncomputable def Policy.meanDuration (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) : ℝ :=
  ∫ ω : World n Seed, π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ν

/-- The pending execution has exactly the mean duration equal to actual reach. -/
theorem Policy.reachProbability_eq_mean_pending (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    π.reachProbability P ν i =
      ∫ ω : World n Seed, π.pendingTime ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw ν := by
  have he : {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i} =ᵐ[P.worldLaw ν]
      {ω | ω.2.1 i ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i} := by
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hω
    exact propext (π.reaches_iff_le_pendingTime _ _ _ i (hω i).2)
  unfold Policy.reachProbability
  rw [measureReal_congr he]
  exact ProphetSecretary.Reach.reach_probability_eq_mean_pending (P.worldLaw ν)
    (π.measurable_pendingWorldTime hπ i)
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    (P.world_clock_map ν i) (P.pendingTime_clock_independent ν π hπ i)
    (P.pendingTime_mem_unitInterval ν π i)

/-- Universal finite part of `lem:monotone-reach`: every measurable online policy
has `qᵢ ≤ 2 E[τ]`. The offer laws may be unbounded and no first moment is required. -/
theorem Policy.reachProbability_le_twice_meanDuration (π : Policy Seed n)
    (hπ : π.IsMeasurable) (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) :
    π.reachProbability P ν i ≤ 2 * π.meanDuration P ν := by
  rw [π.reachProbability_eq_mean_pending hπ P ν i]
  apply ProphetSecretary.Reach.mean_pending_le_twice_duration (P.worldLaw ν)
    (π.measurable_pendingWorldTime hπ i)
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    ((π.measurable_worldTime hπ Finset.univ).aestronglyMeasurable)
    (P.world_clock_map ν i) (P.pendingTime_clock_independent ν π hπ i)
    (P.pendingTime_mem_unitInterval ν π i)
    (P.worldTime_mem_unitInterval ν π Finset.univ)
  filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hω
  exact π.min_le_stoppingTime _ _ _ i (hω i).2

end ProphetSecretary.Model
