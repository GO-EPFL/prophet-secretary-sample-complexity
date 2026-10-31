import ProphetSecretary.Limiting.ConfigurationAppendPoint
import ProphetSecretary.Limiting.CountableDurationValueMonotonicity
import ProphetSecretary.Limiting.FirstAcceptanceOneNewCode

/-!
# One-point insertion in the actual countable execution

The new anonymous occurrence is appended in one construction band. Every
old occurrence retains its analytical label, clock and value. Actual Markov
callbacks read only the retained unseen-identity mask and current offer, so
all old potential actions remain unchanged. Adding at most this one accepted
code can only decrease actual duration. This is not asserted for general
policies that use the anonymous observation history.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def appendAnonymousPoint (k : ℕ) (p : Point) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  (Function.update v.1 k (appendConfigurationPoint (v.1 k) p),v.2)

def appendedCandidate (k : ℕ) (v : CompleteWorld Seed) : Candidate := Sum.inr (k,(v.1 k).1)

lemma appendedCandidate_not_present (k : ℕ) (v : CompleteWorld Seed) :
    ¬candidatePresent v (appendedCandidate k v) := Nat.lt_irrefl _

lemma appendedCandidate_present (k : ℕ) (p : Point) (v : CompleteWorld Seed) :
    candidatePresent (appendAnonymousPoint k p v) (appendedCandidate k v) := by
  change (v.1 k).1 < (Function.update v.1 k (appendConfigurationPoint (v.1 k) p) k).1
  rw [Function.update_self,appendConfigurationPoint_count]
  exact Nat.lt_succ_self _

lemma candidatePoint_appendedCandidate (k : ℕ) (p : Point) (v : CompleteWorld Seed) :
    candidatePoint (appendAnonymousPoint k p v) (appendedCandidate k v)=p := by
  change configurationPoint (v.1 k).1 (Function.update v.1 k (appendConfigurationPoint (v.1 k) p) k)=p
  rw [Function.update_self,configurationPoint_append_last]

lemma candidatePresent_append_of_ne (k : ℕ) (p : Point) (v : CompleteWorld Seed)
    (c : Candidate) (hc : c≠appendedCandidate k v) :
    candidatePresent (appendAnonymousPoint k p v) c ↔ candidatePresent v c := by
  cases c with
  | inl i => rfl
  | inr lj =>
    obtain ⟨l,j⟩ := lj
    by_cases hl : l=k
    · subst l
      have hj : j≠(v.1 k).1 := fun h => hc (congrArg Sum.inr (Prod.ext rfl h))
      change j<(Function.update v.1 k (appendConfigurationPoint (v.1 k) p) k).1 ↔ j<(v.1 k).1
      rw [Function.update_self,appendConfigurationPoint_count]
      omega
    · change j<(Function.update v.1 k (appendConfigurationPoint (v.1 k) p) l).1 ↔ j<(v.1 l).1
      rw [Function.update_of_ne hl]

lemma candidatePoint_append_of_ne (k : ℕ) (p : Point) (v : CompleteWorld Seed)
    (c : Candidate) (hc : c≠appendedCandidate k v) :
    candidatePoint (appendAnonymousPoint k p v) c=candidatePoint v c := by
  cases c with
  | inl i => rfl
  | inr lj =>
    obtain ⟨l,j⟩ := lj
    by_cases hl : l=k
    · subst l
      have hj : j≠(v.1 k).1 := fun h => hc (congrArg Sum.inr (Prod.ext rfl h))
      change configurationPoint j (Function.update v.1 k (appendConfigurationPoint (v.1 k) p) k)=_
      rw [Function.update_self]
      exact configurationPoint_append_of_ne _ p j hj
    · change configurationPoint j (Function.update v.1 k (appendConfigurationPoint (v.1 k) p) l)=_
      rw [Function.update_of_ne hl]
      rfl

lemma countableMarkovRule_action_append_of_ne
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (p : Point) (v : CompleteWorld Seed) (c : Candidate) (hc : c≠appendedCandidate k v) :
    (countableMarkovRule accept).candidateAction (appendAnonymousPoint k p v) c=
      (countableMarkovRule accept).candidateAction v c := by
  rw [countableMarkovRule_candidateAction_eq,countableMarkovRule_candidateAction_eq,
    candidatePoint_append_of_ne k p v c hc]
  rfl

lemma countableMarkovRule_action_appended
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (p : Point) (v : CompleteWorld Seed) :
    (countableMarkovRule accept).candidateAction (appendAnonymousPoint k p v) (appendedCandidate k v)=
      accept v.2.2.2 (clockMask v.2.2.1 p.1) p.1 none p.2 := by
  rw [countableMarkovRule_candidateAction_eq,candidatePoint_appendedCandidate]
  rfl

lemma countableMarkovRule_accepted_append_of_ne
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (p : Point) (v : CompleteWorld Seed) (j : ℕ)
    (hj : j≠candidateEnumeration (appendedCandidate k v)) :
    (countableMarkovRule accept).codeAccepted (appendAnonymousPoint k p v) j ↔
      (countableMarkovRule accept).codeAccepted v j := by
  have hc : candidateEnumeration.symm j≠appendedCandidate k v := by
    intro h
    exact hj (by simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration h)
  have hPoint := candidatePoint_append_of_ne k p v _ hc
  simp only [CountableRule.codeAccepted,codePresent,candidatePresent_append_of_ne k p v _ hc,
    countableMarkovRule_action_append_of_ne accept k p v _ hc,codeTime,codePoint,hPoint]

theorem countableMarkovRule_duration_append_le
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (p : Point) (v : CompleteWorld Seed) :
    (countableMarkovRule accept).realizedDuration (appendAnonymousPoint k p v) ≤
      (countableMarkovRule accept).realizedDuration v := by
  let π := countableMarkovRule accept
  have hNotOld (j : ℕ) (hj : π.codeAccepted v j) : j≠candidateEnumeration (appendedCandidate k v) := by
    intro h
    subst j
    have hPresent := hj.1
    change candidatePresent v (candidateEnumeration.symm (candidateEnumeration (appendedCandidate k v))) at hPresent
    rw [Equiv.symm_apply_apply] at hPresent
    exact appendedCandidate_not_present k v hPresent
  apply FirstAcceptance.stoppingTime_antitone_one_new_code (candidateEnumeration (appendedCandidate k v))
  · intro j hj
    exact (countableMarkovRule_accepted_append_of_ne accept k p v j (hNotOld j hj)).mpr hj
  · intro j hj hNew
    exact (countableMarkovRule_accepted_append_of_ne accept k p v j hj).mp hNew
  · intro j hj
    exact congrArg Prod.fst (candidatePoint_append_of_ne k p v _ (by
      intro he
      exact hNotOld j hj (by simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration he)))
  · intro j hj
    exact hj.2.1.2

theorem valueRule_duration_append_le (B : CountableInstance) (w c : ℝ)
    (k : ℕ) (p : Point) (v : CompleteWorld Unit) :
    (B.valueRule w c).realizedDuration (appendAnonymousPoint k p v) ≤
      (B.valueRule w c).realizedDuration v := by
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_duration_append_le _ k p v

variable [MeasurableSpace Seed]

lemma measurable_appendAnonymousPoint (k : ℕ) :
    Measurable (fun z : CompleteWorld Seed × Point => appendAnonymousPoint k z.2 z.1) := by
  have hCloud : Measurable (fun z : CompleteWorld Seed × Point =>
      Function.update z.1.1 k (appendConfigurationPoint (z.1.1 k) z.2)) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j=k
    · subst j
      have hPair : Measurable (fun z : CompleteWorld Seed × Point => (z.1.1 k,z.2)) :=
        (((measurable_pi_apply k).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
      simpa only [Function.update_self,Function.comp_def] using measurable_appendConfigurationPoint.comp hPair
    · simpa only [Function.update_of_ne hj,Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_fst.comp
          (measurable_fst : Measurable (fun z : CompleteWorld Seed × Point => z.1)))
  exact hCloud.prodMk (measurable_snd.comp measurable_fst)

end ProphetSecretary.Limiting.CountableInstance
