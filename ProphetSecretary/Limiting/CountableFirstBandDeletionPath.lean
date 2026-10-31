import ProphetSecretary.Limiting.CountableFirstBandDeletionLaw
import ProphetSecretary.Limiting.CountableDurationValueMonotonicity

/-!
# Markov execution after deleting finitely many construction bands

Every surviving candidate retains its analytical code, clock and value.
Markov potential actions on those candidates are unchanged. If the original
first acceptance survives, it remains first with the same reward and time.
Original admissibility handles the terminal no-selection case; admissibility
of the transformed execution is not assumed as an interface.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def SurvivesFirstBandDeletion (N : ℕ) : Candidate → Prop
  | Sum.inl _ => True
  | Sum.inr kj => N<kj.1

lemma candidatePresent_eraseFirstBandsWorld (N : ℕ) (v : CompleteWorld Seed) (c : Candidate) :
    candidatePresent (eraseFirstBandsWorld N v) c ↔ candidatePresent v c ∧ SurvivesFirstBandDeletion N c := by
  cases c with
  | inl i => exact ⟨fun _ => ⟨trivial,trivial⟩,fun _ => trivial⟩
  | inr kj =>
    obtain ⟨k,j⟩ := kj
    by_cases hk : k≤N
    · simp only [candidatePresent,eraseFirstBandsWorld,eraseFirstBandConfigurations,if_pos hk,
        emptyConfiguration,configurationMk,SurvivesFirstBandDeletion,Nat.not_lt_zero,not_lt_of_ge hk,and_false]
    · change j<(if k≤N then emptyConfiguration else v.1 k).1 ↔ j<(v.1 k).1 ∧ N<k
      rw [if_neg hk]
      exact ⟨fun h => ⟨h,lt_of_not_ge hk⟩,And.left⟩

lemma candidatePoint_eraseFirstBandsWorld (N : ℕ) (v : CompleteWorld Seed) (c : Candidate)
    (hSurvive : SurvivesFirstBandDeletion N c) :
    candidatePoint (eraseFirstBandsWorld N v) c=candidatePoint v c := by
  cases c with
  | inl i => rfl
  | inr kj =>
    change N<kj.1 at hSurvive
    simp only [candidatePoint,eraseFirstBandsWorld,eraseFirstBandConfigurations,if_neg (not_le.mpr hSurvive)]

lemma countableMarkovRule_action_eraseFirstBandsWorld
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (N : ℕ) (v : CompleteWorld Seed) (c : Candidate) (hSurvive : SurvivesFirstBandDeletion N c) :
    (countableMarkovRule accept).candidateAction (eraseFirstBandsWorld N v) c=
      (countableMarkovRule accept).candidateAction v c := by
  rw [countableMarkovRule_candidateAction_eq,countableMarkovRule_candidateAction_eq,
    candidatePoint_eraseFirstBandsWorld N v c hSurvive]
  rfl

lemma countableMarkovRule_accepted_eraseFirstBandsWorld_iff
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (N : ℕ) (v : CompleteWorld Seed) (i : ℕ)
    (hSurvive : SurvivesFirstBandDeletion N (candidateEnumeration.symm i)) :
    (countableMarkovRule accept).codeAccepted (eraseFirstBandsWorld N v) i ↔
      (countableMarkovRule accept).codeAccepted v i := by
  have hPresent : candidatePresent (eraseFirstBandsWorld N v) (candidateEnumeration.symm i) ↔
      candidatePresent v (candidateEnumeration.symm i) := by
    constructor
    · intro hp
      exact ((candidatePresent_eraseFirstBandsWorld N v _).mp hp).1
    · intro hp
      exact (candidatePresent_eraseFirstBandsWorld N v _).mpr ⟨hp,hSurvive⟩
  have hPoint := candidatePoint_eraseFirstBandsWorld N v _ hSurvive
  simp only [CountableRule.codeAccepted,codePresent,hPresent,codeTime,codePoint,hPoint,
    countableMarkovRule_action_eraseFirstBandsWorld accept N v _ hSurvive]

lemma countableMarkovRule_accepted_eraseFirstBandsWorld_subset
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (N : ℕ) (v : CompleteWorld Seed) (i : ℕ)
    (hi : (countableMarkovRule accept).codeAccepted (eraseFirstBandsWorld N v) i) :
    (countableMarkovRule accept).codeAccepted v i ∧ SurvivesFirstBandDeletion N (candidateEnumeration.symm i) := by
  have hSurvive := ((candidatePresent_eraseFirstBandsWorld N v _).mp hi.1).2
  exact ⟨(countableMarkovRule_accepted_eraseFirstBandsWorld_iff accept N v i hSurvive).mp hi,hSurvive⟩

lemma countableMarkovRule_earliest_eraseFirstBandsWorld
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (N : ℕ) (v : CompleteWorld Seed) (i : ℕ)
    (hi : FirstAcceptance.Earliest (countableMarkovRule accept).codeAccepted codeTime v i)
    (hSurvive : SurvivesFirstBandDeletion N (candidateEnumeration.symm i)) :
    FirstAcceptance.Earliest (countableMarkovRule accept).codeAccepted codeTime (eraseFirstBandsWorld N v) i := by
  refine ⟨(countableMarkovRule_accepted_eraseFirstBandsWorld_iff accept N v i hSurvive).mpr hi.1,?_⟩
  intro j hj
  have hOld := countableMarkovRule_accepted_eraseFirstBandsWorld_subset accept N v j hj
  have hOrder := hi.2 j hOld.1
  have hI := congrArg Prod.fst (candidatePoint_eraseFirstBandsWorld N v _ hSurvive)
  have hJ := congrArg Prod.fst (candidatePoint_eraseFirstBandsWorld N v _ hOld.2)
  change codeTime (eraseFirstBandsWorld N v) i=codeTime v i at hI
  change codeTime (eraseFirstBandsWorld N v) j=codeTime v j at hJ
  rw [hI,hJ]
  exact hOrder

theorem countableMarkovRule_outcomes_eraseFirstBandsWorld
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (N : ℕ) (a : ℝ) (v : CompleteWorld Seed)
    (hFirst : FirstAcceptance.HasFirstIfAccepted (countableMarkovRule accept).codeAccepted codeTime v)
    (hSurvive : ∀ i, FirstAcceptance.Earliest (countableMarkovRule accept).codeAccepted codeTime v i →
      SurvivesFirstBandDeletion N (candidateEnumeration.symm i)) :
    (countableMarkovRule accept).realizedReward a (eraseFirstBandsWorld N v)=
        (countableMarkovRule accept).realizedReward a v ∧
      (countableMarkovRule accept).realizedDuration (eraseFirstBandsWorld N v)=
        (countableMarkovRule accept).realizedDuration v := by
  let π := countableMarkovRule accept
  by_cases hOld : ∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime v i
  · obtain ⟨i,hi⟩ := hOld
    have hNew := countableMarkovRule_earliest_eraseFirstBandsWorld accept N v i hi (hSurvive i hi)
    have hPoint := candidatePoint_eraseFirstBandsWorld N v _ (hSurvive i hi)
    constructor
    · change FirstAcceptance.reward a π.codeAccepted codeTime codeValue (eraseFirstBandsWorld N v)=
        FirstAcceptance.reward a π.codeAccepted codeTime codeValue v
      rw [FirstAcceptance.reward_of_earliest a hNew,FirstAcceptance.reward_of_earliest a hi]
      exact congrArg Prod.snd hPoint
    · change FirstAcceptance.stoppingTime π.codeAccepted codeTime (eraseFirstBandsWorld N v)=
        FirstAcceptance.stoppingTime π.codeAccepted codeTime v
      rw [FirstAcceptance.stoppingTime_of_earliest hNew,FirstAcceptance.stoppingTime_of_earliest hi]
      exact congrArg Prod.fst hPoint
  · have hNone := (FirstAcceptance.no_first_iff_no_accepted hFirst).mp hOld
    have hNew : ¬∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime (eraseFirstBandsWorld N v) i := by
      rintro ⟨i,hi⟩
      exact hNone ⟨i,(countableMarkovRule_accepted_eraseFirstBandsWorld_subset accept N v i hi.1).1⟩
    constructor
    · rw [π.no_first_reward a _ hNew,π.no_first_reward a _ hOld]
    · change FirstAcceptance.stoppingTime π.codeAccepted codeTime (eraseFirstBandsWorld N v)=
        FirstAcceptance.stoppingTime π.codeAccepted codeTime v
      rw [FirstAcceptance.stoppingTime_of_no_first hNew,FirstAcceptance.stoppingTime_of_no_first hOld]

end ProphetSecretary.Limiting.CountableInstance
