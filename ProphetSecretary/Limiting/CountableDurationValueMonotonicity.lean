import ProphetSecretary.Limiting.CountableValueReplacement
import ProphetSecretary.Limiting.FirstAcceptanceSingleAddition
import ProphetSecretary.Limiting.CountableCanonicalReach
import ProphetSecretary.Limiting.CountableValueTies

/-!
# Canonical duration is antitone in one individual offer

The fixed Markov rule reads past identities and times but not past values.
Replacing Xi therefore changes only its own potential action. Raising that
value can only add its accepted code; a single addition preserves an attained
first acceptance. No value monotonicity is asserted for general causal policies
or for a policy reoptimized after changing the individual law.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def UpwardCountableAcceptance (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) : Prop :=
  ∀ r A t i a b, a ≤ b → accept r A t i a=true → accept r A t i b=true

lemma countableMarkovRule_candidateAction_eq
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (v : CompleteWorld Seed) (c : Candidate) :
    (countableMarkovRule accept).candidateAction v c=
      accept v.2.2.2 (clockMask v.2.2.1 (candidatePoint v c).1) (candidatePoint v c).1 (candidateKind c) (candidatePoint v c).2 := by
  cases c <;> simp only [CountableRule.candidateAction,countableMarkovRule,candidateKind,
    unseenMask_history_eq_clockMask]

lemma countableMarkovRule_candidateAction_replaceValue_of_ne
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (i : ℕ)
    (z : CompleteWorld Seed × ℝ) (c : Candidate) (hc : c ≠ Sum.inl i) :
    (countableMarkovRule accept).candidateAction (replaceIndividualValue i z) c=
      (countableMarkovRule accept).candidateAction z.1 c := by
  rw [countableMarkovRule_candidateAction_eq,countableMarkovRule_candidateAction_eq,
    candidatePoint_replaceIndividualValue_of_ne i z c hc]
  rfl

lemma countableMarkovRule_codeAccepted_replaceValue_of_ne
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (i : ℕ)
    (z : CompleteWorld Seed × ℝ) (k : ℕ) (hk : k ≠ candidateEnumeration (Sum.inl i)) :
    (countableMarkovRule accept).codeAccepted (replaceIndividualValue i z) k ↔
      (countableMarkovRule accept).codeAccepted z.1 k := by
  have hc : candidateEnumeration.symm k ≠ Sum.inl i := by
    intro h
    apply hk
    simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration h
  have hPoint : codePresent (replaceIndividualValue i z) k ↔ codePresent z.1 k :=
    candidatePresent_replaceIndividualValue i z _
  simp only [CountableRule.codeAccepted,hPoint,codeTime_replaceIndividualValue,
    countableMarkovRule_candidateAction_replaceValue_of_ne accept i z _ hc]

lemma countableMarkovRule_codeAccepted_mono_candidateValue
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (hUp : UpwardCountableAcceptance accept)
    (i : ℕ) (v : CompleteWorld Seed) {a b : ℝ} (hab : a ≤ b) (k : ℕ)
    (hA : (countableMarkovRule accept).codeAccepted (replaceIndividualValue i (v,a)) k) :
    (countableMarkovRule accept).codeAccepted (replaceIndividualValue i (v,b)) k := by
  by_cases hk : k=candidateEnumeration (Sum.inl i)
  · subst k
    have hClock : codeTime (replaceIndividualValue i (v,b)) (candidateEnumeration (Sum.inl i))=
        codeTime (replaceIndividualValue i (v,a)) (candidateEnumeration (Sum.inl i)) :=
      (codeTime_replaceIndividualValue i (v,b) _).trans (codeTime_replaceIndividualValue i (v,a) _).symm
    refine ⟨individual_candidate_present _ i,?_,?_⟩
    · rw [hClock]
      exact hA.2.1
    · have hAction := hA.2.2
      simp only [Equiv.symm_apply_apply,countableMarkovRule_candidateAction_eq,candidatePoint,
        replaceIndividualValue,Function.update_self,candidateKind] at hAction ⊢
      exact hUp _ _ _ _ a b hab hAction
  · exact (countableMarkovRule_codeAccepted_replaceValue_of_ne accept i (v,b) k hk).mpr
      ((countableMarkovRule_codeAccepted_replaceValue_of_ne accept i (v,a) k hk).mp hA)

theorem countableMarkovRule_duration_antitone_candidateValue
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (hUp : UpwardCountableAcceptance accept)
    (i : ℕ) (v : CompleteWorld Seed) :
    Antitone (fun x => (countableMarkovRule accept).realizedDuration (replaceIndividualValue i (v,x))) := by
  intro a b hab
  apply FirstAcceptance.stoppingTime_antitone_single_addition (candidateEnumeration (Sum.inl i))
  · intro k
    exact (codeTime_replaceIndividualValue i (v,b) k).trans (codeTime_replaceIndividualValue i (v,a) k).symm
  · exact countableMarkovRule_codeAccepted_mono_candidateValue accept hUp i v hab
  · intro k hk hB
    exact (countableMarkovRule_codeAccepted_replaceValue_of_ne accept i (v,a) k hk).mpr
      ((countableMarkovRule_codeAccepted_replaceValue_of_ne accept i (v,b) k hk).mp hB)
  · intro k hk
    exact hk.2.1.2

lemma valueMarkovAcceptance_upward (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) :
    UpwardCountableAcceptance (B.valueMarkovAcceptance w c) := by
  intro r A t i a b hab hA
  have h : 0 < a ∧ B.continuationValue (candidateMask A i) w c (remainingTime t) ≤ w*a := of_decide_eq_true hA
  exact decide_eq_true ⟨h.1.trans_le hab,h.2.trans (mul_le_mul_of_nonneg_left hab hw)⟩

/-- The canonical design instance remains fixed throughout this comparison. -/
theorem canonical_duration_antitone_candidateValue (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w)
    (i : ℕ) (v : CompleteWorld Unit) :
    Antitone (fun x => (B.valueRule w c).realizedDuration (replaceIndividualValue i (v,x))) := by
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_duration_antitone_candidateValue _ (B.valueMarkovAcceptance_upward hw) i v

end ProphetSecretary.Limiting.CountableInstance
