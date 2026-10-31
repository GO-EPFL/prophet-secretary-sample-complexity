import ProphetSecretary.Limiting.CountableMarkovPointSets
import ProphetSecretary.Limiting.CountablePendingDuration
import ProphetSecretary.Limiting.FirstAcceptanceInfimumComparison

/-!
# Analytical duration for one-point insertion

The accepted-time infimum is measurable and unit bounded on all worlds. Its
insertion and relabeling comparisons therefore require no admissibility on
an inserted-point slice. On the original admissible law it is the actual
stopping duration, so it can be used in the Poisson response calculation.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

theorem countableMarkovRule_infimumDuration_append_le
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (p : Point) (v : CompleteWorld Seed) :
    (countableMarkovRule accept).infimumDuration (appendAnonymousPoint k p v) ≤
      (countableMarkovRule accept).infimumDuration v := by
  apply FirstAcceptance.infimumTime_le_of_accepted_times_inclusion (fun _ h => h.2.1) (fun _ h => h.2.1)
  intro j hj
  have hNe : j≠candidateEnumeration (appendedCandidate k v) := by
    intro he
    subst j
    have hPresent := hj.1
    change candidatePresent v (candidateEnumeration.symm (candidateEnumeration (appendedCandidate k v))) at hPresent
    rw [Equiv.symm_apply_apply] at hPresent
    exact appendedCandidate_not_present k v hPresent
  refine ⟨j,(countableMarkovRule_accepted_append_of_ne accept k p v j hNe).mpr hj,?_⟩
  exact (congrArg Prod.fst (candidatePoint_append_of_ne k p v _ (by
    intro he
    exact hNe (by simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration he)))).symm

theorem countableMarkovRule_infimumDuration_cloud_ranges_congr
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (ω ξ : BandConfigurations) (a : (ℕ → ℝ) × ((ℕ → ℝ) × Seed))
    (hRange : ∀ k, Set.range (ω k).2=Set.range (ξ k).2) :
    (countableMarkovRule accept).infimumDuration (ω,a)=
      (countableMarkovRule accept).infimumDuration (ξ,a) := by
  exact FirstAcceptance.infimumTime_eq_of_accepted_times_eq (fun _ h => h.2.1) (fun _ h => h.2.1)
    (countableMarkovRule_accepted_match_of_cloud_ranges_eq accept ω ξ a hRange)
    (countableMarkovRule_accepted_match_of_cloud_ranges_eq accept ξ ω a (fun k => (hRange k).symm))

theorem countableMarkovRule_infimumDuration_append_erased
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (v : CompleteWorld Seed) (j : Fin (v.1 k).1) :
    (countableMarkovRule accept).infimumDuration
      (appendAnonymousPoint k ((v.1 k).2 j) (eraseAnonymousPoint k v j))=
      (countableMarkovRule accept).infimumDuration v := by
  apply countableMarkovRule_infimumDuration_cloud_ranges_congr
  intro l
  by_cases hl : l=k
  · subst l
    dsimp only [appendAnonymousPoint,eraseAnonymousPoint]
    rw [Function.update_self,Function.update_self]
    exact range_append_erasedPoint (v.1 k) j
  · dsimp only [appendAnonymousPoint,eraseAnonymousPoint]
    rw [Function.update_of_ne hl,Function.update_of_ne hl]

theorem valueRule_infimumDuration_append_le (B : CountableInstance) (w c : ℝ)
    (k : ℕ) (p : Point) (v : CompleteWorld Unit) :
    (B.valueRule w c).infimumDuration (appendAnonymousPoint k p v) ≤
      (B.valueRule w c).infimumDuration v := by
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_infimumDuration_append_le _ k p v

theorem valueRule_infimumDuration_append_erased (B : CountableInstance) (w c : ℝ)
    (k : ℕ) (v : CompleteWorld Unit) (j : Fin (v.1 k).1) :
    (B.valueRule w c).infimumDuration
      (appendAnonymousPoint k ((v.1 k).2 j) (eraseAnonymousPoint k v j))=
      (B.valueRule w c).infimumDuration v := by
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_infimumDuration_append_erased _ k v j

end ProphetSecretary.Limiting.CountableInstance
