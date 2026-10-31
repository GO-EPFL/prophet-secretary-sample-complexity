import ProphetSecretary.Limiting.CountableReachValue
import ProphetSecretary.Limiting.CountableSelection
import ProphetSecretary.Limiting.CountableClockNullSets

/-!
# Accepted reached value sets yield individual selection mass

Reach is independent of the candidate value under the actual full product law.
If the current callback accepts on a reached value set, admissibility and
clock injectivity identify that individual as the selected occurrence. The
result applies to arbitrary policies and includes cap atoms and upper tails.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma CountableRule.selectsIndividual_of_reached_accepted (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed)
    (hFirst : FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime v)
    (hClock : Set.InjOn (fun c : Candidate => (candidatePoint v c).1) {c | candidatePresent v c})
    (hReach : v.2.2.1 i ≤ π.realizedDuration v)
    (hAccepted : π.codeAccepted v (candidateEnumeration (Sum.inl i))) : π.SelectsIndividual v i := by
  obtain ⟨k,hk⟩ := hFirst ⟨candidateEnumeration (Sum.inl i),hAccepted⟩
  have hτ : π.realizedDuration v=codeTime v k := FirstAcceptance.stoppingTime_of_earliest hk
  have hLe : codeTime v k ≤ v.2.2.1 i :=
    (hk.2 (candidateEnumeration (Sum.inl i)) hAccepted).1.trans_eq (codeTime_individual i v)
  have hEq : v.2.2.1 i=codeTime v k := le_antisymm (hReach.trans_eq hτ) hLe
  have hCandidate : Sum.inl i=candidateEnumeration.symm k :=
    hClock (show candidatePresent v (Sum.inl i) from trivial)
      (show candidatePresent v (candidateEnumeration.symm k) from hk.1.1) hEq
  have hCode : candidateEnumeration (Sum.inl i)=k := by
    simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration hCandidate
  change FirstAcceptance.Earliest π.codeAccepted codeTime v (candidateEnumeration (Sum.inl i))
  rw [hCode]
  exact hk

variable [MeasurableSpace Seed]

theorem CountableRule.individualSelectionProbability_ge_reach_mul_valueMass
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (hAdm : π.Admissible B ν) (i : ℕ)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hAccept : ∀ᵐ v ∂B.completeWorldLaw ν, v.2.2.1 i ≤ π.realizedDuration v → v.2.1 i ∈ S →
      π.candidateAction v (Sum.inl i)=true) :
    π.individualSelectionProbability B ν i ≥ π.individualReachProbability B ν i*(B.individuals i : Measure ℝ).real S := by
  have hSub : ∀ᵐ v ∂B.completeWorldLaw ν,
      (v.2.2.1 i ≤ π.realizedDuration v ∧ v.2.1 i ∈ S) → π.SelectsIndividual v i := by
    filter_upwards [hAdm,B.present_candidate_times_injective ν,B.present_candidate_times_mem_Ioo ν,hAccept]
      with v hFirst hInj hTimes hA hv
    have ht := hTimes (Sum.inl i) trivial
    have hAccepted : π.codeAccepted v (candidateEnumeration (Sum.inl i)) := by
      refine ⟨individual_candidate_present v i,?_,?_⟩
      · rw [codeTime_individual]
        exact ⟨ht.1.le,ht.2.le⟩
      · simpa only [Equiv.symm_apply_apply] using hA hv.1 hv.2
    exact π.selectsIndividual_of_reached_accepted i v hFirst hInj hv.1 hAccepted
  have hProb := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hSub)
  change (B.completeWorldLaw ν).real {v | v.2.2.1 i ≤ π.realizedDuration v ∧ v.2.1 i ∈ S} ≤
    π.individualSelectionProbability B ν i at hProb
  rw [π.reach_value_probability hπ B ν hAdm i hS] at hProb
  exact hProb

end ProphetSecretary.Limiting.CountableInstance

namespace ProphetSecretary.Limiting.RandomizedCountablePolicy
open CountableInstance
variable {B : CountableInstance}

theorem individualSelectionProbability_ge_reach_mul_valueMass (π : RandomizedCountablePolicy B)
    (i : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (hAccept : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, v.2.2.1 i ≤ π.rule.realizedDuration v → v.2.1 i ∈ S →
      π.rule.candidateAction v (Sum.inl i)=true) :
    π.individualSelectionProbability i ≥ π.individualReachProbability i*(B.individuals i : Measure ℝ).real S :=
  π.rule.individualSelectionProbability_ge_reach_mul_valueMass π.measurable_rule B π.seedLaw π.admissible i hS hAccept

theorem individualSelectionProbability_ge_reach_mul_atom (π : RandomizedCountablePolicy B)
    (i : ℕ) (x : ℝ)
    (hAccept : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, v.2.2.1 i ≤ π.rule.realizedDuration v → v.2.1 i=x →
      π.rule.candidateAction v (Sum.inl i)=true) :
    π.individualSelectionProbability i ≥ π.individualReachProbability i*(B.individuals i : Measure ℝ).real {x} := by
  apply π.individualSelectionProbability_ge_reach_mul_valueMass i (measurableSet_singleton x)
  filter_upwards [hAccept] with v hv hR hx
  exact hv hR (Set.mem_singleton_iff.mp hx)

end ProphetSecretary.Limiting.RandomizedCountablePolicy
