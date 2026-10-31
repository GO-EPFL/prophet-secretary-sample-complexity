import ProphetSecretary.Reach.ZeroReach
import ProphetSecretary.Reach.ClockDiscrepancy
import ProphetSecretary.Model.Restriction
import ProphetSecretary.Model.ZeroSimulationProbability

/-!
# Zero offers convert reach into duration

Paper correspondence: `lem:zeros`, finite-instance statement. The duration error is
explicitly `20 / sqrt N`, uniformly over arbitrary measurable randomized policies that
observe every zero identity and timestamp. The policy simulation is constructed in
`ZeroSimulation`, and its independent-clock law transport is proved separately.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

namespace Instance

variable {n m : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- An arbitrary injected subvector of clocks keeps its independent uniform product law,
even when the policy may use all observations and its independent seed. -/
theorem world_restrictedClocks_measurePreserving (P : Instance n) (e : Fin m ↪ Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun ω : World n Seed => ω.2.1 ∘ e) (P.worldLaw ν) (clocksLaw m) :=
  (restrictClocks_measurePreserving e).comp
    ((measurePreserving_fst (μ := clocksLaw n) (ν := ν)).comp
      (measurePreserving_snd (μ := P.valuesLaw) (ν := (clocksLaw n).prod ν)))

theorem mean_world_clockFunctional_eq (P : Instance n) (e : Fin m ↪ Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (g : (Fin m → ℝ) → ℝ) (hg : Measurable g) :
    (∫ ω : World n Seed, g (ω.2.1 ∘ e) ∂P.worldLaw ν) = ∫ u, g u ∂clocksLaw m := by
  have hp := P.world_restrictedClocks_measurePreserving e ν
  have h := integral_map (μ := P.worldLaw ν) hp.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm

/-- The clock discrepancy is averaged over exactly the `N` appended clocks. -/
theorem mean_zeroClockDiscrepancy_eq {n N : ℕ} (P : Instance (n + N))
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ ω : World (n + N) Seed,
      ProphetSecretary.Reach.ZeroReach.discrepancy (fun j : Fin N => ω.2.1 (Fin.natAdd n j)) ∂P.worldLaw ν) =
        ∫ z : Fin N → ℝ, ProphetSecretary.Reach.ZeroReach.discrepancy z ∂clocksLaw N :=
  P.mean_world_clockFunctional_eq (Fin.natAddEmb n) ν _
    (ProphetSecretary.Reach.ZeroReach.measurable_discrepancy (fun i => measurable_pi_apply i))

end Instance

variable {Seed : Type*} [MeasurableSpace Seed] {n N : ℕ}

/-- Uniform duration estimate, valid for any chosen appended identities and arbitrary
online decisions. Their values do not enter this stronger quantitative statement. -/
theorem Policy.meanDuration_ge_common_zeroReach_sub_sqrt
    (π : Policy Seed (n + N)) (hπ : π.IsMeasurable) (hN : 0 < N)
    (P : Instance (n + N)) (ν : Measure Seed) [IsProbabilityMeasure ν] (ρ : ℝ)
    (hq : ∀ j : Fin N, ρ ≤ π.reachProbability P ν (Fin.natAdd n j)) :
    ρ - 20 / Real.sqrt (N : ℝ) ≤ π.meanDuration P ν := by
  have h := π.meanDuration_ge_common_zeroReach_sub_discrepancy hπ hN P ν ρ hq
  rw [P.mean_zeroClockDiscrepancy_eq ν] at h
  have hd := ProphetSecretary.Reach.ZeroReach.expected_uniform_discrepancy_le N hN
  linarith

/-- `lem:zeros` with an explicit universal constant. The two reward integrability
conclusions record the first-moment obligations for the expectation-preserving simulation. -/
theorem finite_zero_comparison (P : Instance n) (N : ℕ) (hN : 0 < N)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : RandomizedPolicy (n + N)) (ρ : ℝ)
    (hq : ∀ j : Fin N, ρ ≤ π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) :
    ρ - 20 / Real.sqrt (N : ℝ) ≤ π.expectedDuration (P.appendZeros N) ∧
      Integrable π.realizedReward ((P.appendZeros N).worldLaw π.seedLaw) ∧
      Integrable (π.simulateZeros).realizedReward (P.worldLaw (π.simulateZeros).seedLaw) ∧
      (π.simulateZeros).expectedReward P = π.expectedReward (P.appendZeros N) ∧
      π.expectedDuration (P.appendZeros N) ≤ (π.simulateZeros).expectedDuration P := by
  exact ⟨π.rule.meanDuration_ge_common_zeroReach_sub_sqrt π.measurable_rule hN
      (P.appendZeros N) π.seedLaw ρ hq,
    π.integrable_realizedReward (P.appendZeros N) (P.appendZeros_integrable_maximum N hP),
    (π.simulateZeros).integrable_realizedReward P hP,
    π.simulateZeros_expectedReward P, π.simulateZeros_expectedDuration P⟩

end ProphetSecretary.Model
