import ProphetSecretary.Limiting.CountableAppendPoint
import ProphetSecretary.Limiting.FirstAcceptanceTimeSetCongruence
import ProphetSecretary.Limiting.ConfigurationAppendRange

/-!
# Markov duration is invariant under anonymous array relabeling

With the individual vector, clocks and seed fixed, equality of each band's
point set gives equality of accepted physical-time sets. Markov callbacks
ignore the anonymous past and construction labels. The attained first time,
including its terminal default, is consequently unchanged. In particular,
appending a deleted distinguished point recovers the original duration.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma candidate_match_of_cloud_ranges_eq (ω ξ : BandConfigurations)
    (a : (ℕ → ℝ) × ((ℕ → ℝ) × Seed))
    (hRange : ∀ k, Set.range (ω k).2=Set.range (ξ k).2)
    (c : Candidate) (hc : candidatePresent (ω,a) c) :
    ∃ d : Candidate, candidatePresent (ξ,a) d ∧
      candidatePoint (ω,a) c=candidatePoint (ξ,a) d ∧ candidateKind c=candidateKind d := by
  cases c with
  | inl i => exact ⟨Sum.inl i,trivial,rfl,rfl⟩
  | inr kj =>
    obtain ⟨k,j⟩ := kj
    change j<(ω k).1 at hc
    have hMem : (ω k).2 ⟨j,hc⟩ ∈ Set.range (ξ k).2 := by
      rw [← hRange k]
      exact ⟨⟨j,hc⟩,rfl⟩
    obtain ⟨l,hl⟩ := hMem
    refine ⟨Sum.inr (k,l.val),l.isLt,?_,rfl⟩
    simp only [candidatePoint,configurationPoint,dif_pos hc,dif_pos l.isLt]
    exact hl.symm

lemma countableMarkovRule_accepted_match_of_cloud_ranges_eq
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (ω ξ : BandConfigurations) (a : (ℕ → ℝ) × ((ℕ → ℝ) × Seed))
    (hRange : ∀ k, Set.range (ω k).2=Set.range (ξ k).2)
    (j : ℕ) (hj : (countableMarkovRule accept).codeAccepted (ω,a) j) :
    ∃ l, (countableMarkovRule accept).codeAccepted (ξ,a) l ∧ codeTime (ω,a) j=codeTime (ξ,a) l := by
  obtain ⟨d,hPresent,hPoint,hKind⟩ := candidate_match_of_cloud_ranges_eq ω ξ a hRange
    (candidateEnumeration.symm j) hj.1
  have hAction : (countableMarkovRule accept).candidateAction (ω,a) (candidateEnumeration.symm j)=
      (countableMarkovRule accept).candidateAction (ξ,a) d := by
    rw [countableMarkovRule_candidateAction_eq,countableMarkovRule_candidateAction_eq,hPoint,hKind]
  refine ⟨candidateEnumeration d,⟨?_,?_,?_⟩,?_⟩
  · simpa only [codePresent,Equiv.symm_apply_apply] using hPresent
  · change (candidatePoint (ξ,a) (candidateEnumeration.symm (candidateEnumeration d))).1 ∈ Icc (0 : ℝ) 1
    rw [Equiv.symm_apply_apply,← hPoint]
    exact hj.2.1
  · simpa only [Equiv.symm_apply_apply] using hAction.symm.trans hj.2.2
  · simpa only [codeTime,codePoint,Equiv.symm_apply_apply] using congrArg Prod.fst hPoint

theorem countableMarkovRule_duration_cloud_ranges_congr
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (ω ξ : BandConfigurations) (a : (ℕ → ℝ) × ((ℕ → ℝ) × Seed))
    (hRange : ∀ k, Set.range (ω k).2=Set.range (ξ k).2) :
    (countableMarkovRule accept).realizedDuration (ω,a)=
      (countableMarkovRule accept).realizedDuration (ξ,a) := by
  apply FirstAcceptance.stoppingTime_eq_of_accepted_times_eq
  · exact countableMarkovRule_accepted_match_of_cloud_ranges_eq accept ω ξ a hRange
  · exact countableMarkovRule_accepted_match_of_cloud_ranges_eq accept ξ ω a (fun k => (hRange k).symm)

def eraseAnonymousPoint (k : ℕ) (v : CompleteWorld Seed) (j : Fin (v.1 k).1) : CompleteWorld Seed :=
  (Function.update v.1 k (erasePoint (v.1 k) j),v.2)

theorem countableMarkovRule_duration_append_erased
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (v : CompleteWorld Seed) (j : Fin (v.1 k).1) :
    (countableMarkovRule accept).realizedDuration
      (appendAnonymousPoint k ((v.1 k).2 j) (eraseAnonymousPoint k v j))=
      (countableMarkovRule accept).realizedDuration v := by
  apply countableMarkovRule_duration_cloud_ranges_congr
  intro l
  by_cases hl : l=k
  · subst l
    dsimp only [appendAnonymousPoint,eraseAnonymousPoint]
    rw [Function.update_self,Function.update_self]
    exact range_append_erasedPoint (v.1 k) j
  · dsimp only [appendAnonymousPoint,eraseAnonymousPoint]
    rw [Function.update_of_ne hl,Function.update_of_ne hl]

theorem valueRule_duration_append_erased (B : CountableInstance) (w c : ℝ)
    (k : ℕ) (v : CompleteWorld Unit) (j : Fin (v.1 k).1) :
    (B.valueRule w c).realizedDuration
      (appendAnonymousPoint k ((v.1 k).2 j) (eraseAnonymousPoint k v j))=
      (B.valueRule w c).realizedDuration v := by
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_duration_append_erased _ k v j

end ProphetSecretary.Limiting.CountableInstance
