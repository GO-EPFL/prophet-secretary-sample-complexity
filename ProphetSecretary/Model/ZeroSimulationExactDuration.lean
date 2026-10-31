import ProphetSecretary.Model.ZeroSimulationProbability
import Mathlib.Probability.HasLaw

/-!
# Exact duration for zero-rejecting simulated policies

A general simulated policy can postpone stopping after a padded zero was
accepted. If all padded-zero actions are false, no such postponement occurs.
The simulator retains independent zero clocks internally and presents only
their strict past through the proved causal history construction.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace ProphetSecretary.Model.ZeroSimulation
variable {n m : ℕ} {Seed : Type*}

lemma stoppingTime_eq_simulated_of_no_zero_action (π : Policy Seed (n+m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ)
    (hZero : ∀ j : Fin m, π.action r Finset.univ (appendValues x) (appendClocks u z) (j.natAdd n)≠true) :
    π.stoppingTime r Finset.univ (appendValues x) (appendClocks u z)=
      (simulate π).stoppingTime (r,z) Finset.univ x u := by
  apply le_antisymm (stoppingTime_le_simulated π r x u z)
  apply (π.le_stoppingTime_iff r Finset.univ (appendValues x) (appendClocks u z) _).mpr
  refine ⟨(simulate π).stoppingTime_le_one (r,z) Finset.univ x u,?_⟩
  intro k hk
  induction k using Fin.addCases with
  | left i =>
    have ha := ((π.mem_accepted r Finset.univ (appendValues x) (appendClocks u z) (i.castAdd m)).mp hk).2
    have hNo : noZeroBefore π r x u z (u i) := by
      rintro ⟨j,_hj,hjAct⟩
      exact hZero j hjAct
    have hAct := (simulate_action_iff π r x u z i).mpr ⟨ha,hNo⟩
    have hAcc := ((simulate π).mem_accepted (r,z) Finset.univ x u i).mpr ⟨Finset.mem_univ _,hAct⟩
    simpa only [appendClocks,Fin.addCases_left] using
      (simulate π).stoppingTime_le_of_accepted (r,z) Finset.univ x u i hAcc
  | right j =>
    exact (hZero j ((π.mem_accepted r Finset.univ (appendValues x) (appendClocks u z) (j.natAdd n)).mp hk).2).elim
end ProphetSecretary.Model.ZeroSimulation

namespace ProphetSecretary.Model.RandomizedPolicy
variable {n m : ℕ}

lemma simulateZeros_expectedDuration_eq_of_no_zero_action (π : RandomizedPolicy (n+m)) (P : Instance n)
    (hZero : ∀ᵐ ω ∂(P.appendZeros m).worldLaw π.seedLaw, ∀ j : Fin m,
      π.rule.action ω.2.2 Finset.univ ω.1 ω.2.1 (j.natAdd n)≠true) :
    (simulateZeros π).expectedDuration P=π.expectedDuration (P.appendZeros m) := by
  have hMP := P.augmentZeroWorld_measurePreserving π.seedLaw m
  have hNo := hMP.quasiMeasurePreserving.ae hZero
  have he := hMP.hasLaw.integral_comp π.measurable_realizedDuration.aestronglyMeasurable
  change (∫ ω, (simulateZeros π).realizedDuration ω ∂P.worldLaw (π.seedLaw.prod (Instance.clocksLaw m))) = _
  calc
    _ = ∫ ω, π.realizedDuration (Instance.augmentZeroWorld ω) ∂P.worldLaw (π.seedLaw.prod (Instance.clocksLaw m)) := by
      apply integral_congr_ae
      filter_upwards [hNo] with ω hω
      exact (ZeroSimulation.stoppingTime_eq_simulated_of_no_zero_action π.rule ω.2.2.1 ω.1 ω.2.1 ω.2.2.2 hω).symm
    _ = _ := he
end ProphetSecretary.Model.RandomizedPolicy
