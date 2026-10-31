import ProphetSecretary.Limiting.CountableIndividualPayloadExecution

/-!
# Selected outcomes under causal payload reconstruction

The reconstructed old execution has the same accepted codes and clocks.
Its value differs only at the affected individual, yielding the exact selected
reward displacement and preserving the convention when no offer is selected.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed U T : Type*}

lemma codeTime_recoverIndividualPayload (i : ℕ) (F : ℝ × U → ℝ × T)
    (v : CompleteWorld (Seed × U)) (k : ℕ) : codeTime (recoverIndividualPayloadWorld i F v) k=codeTime v k := by
  unfold codeTime codePoint
  cases candidateEnumeration.symm k <;> rfl

lemma codePresent_recoverIndividualPayload (i : ℕ) (F : ℝ × U → ℝ × T)
    (v : CompleteWorld (Seed × U)) (k : ℕ) : codePresent (recoverIndividualPayloadWorld i F v) k ↔ codePresent v k := by
  unfold codePresent
  cases candidateEnumeration.symm k <;> rfl

lemma codeValue_recoverIndividualPayload (i : ℕ) (F : ℝ × U → ℝ × T)
    (v : CompleteWorld (Seed × U)) (k : ℕ) :
    codeValue (recoverIndividualPayloadWorld i F v) k=
      if k=candidateEnumeration (Sum.inl i) then (F (v.2.1 i,v.2.2.2.2)).1 else codeValue v k := by
  have hValue : codeValue (recoverIndividualPayloadWorld i F v) k=
      codeValue (replaceIndividualValue i (v,(F (v.2.1 i,v.2.2.2.2)).1)) k := by
    unfold codeValue codePoint
    cases candidateEnumeration.symm k <;> rfl
  exact hValue.trans (codeValue_replaceIndividualValue i v (F (v.2.1 i,v.2.2.2.2)).1 k)

lemma CountableRule.pullbackIndividualPayload_codeAccepted (π : CountableRule (Seed × T)) (i : ℕ)
    (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i)
    (v : CompleteWorld (Seed × U)) (k : ℕ) :
    (π.pullbackIndividualPayload i F t0).codeAccepted v k ↔
      π.codeAccepted (recoverIndividualPayloadWorld i F v) k := by
  simp only [CountableRule.codeAccepted,CountableRule.pullbackIndividualPayload_candidateAction π i F t0 hBlind,
    codeTime_recoverIndividualPayload,codePresent_recoverIndividualPayload]

lemma CountableRule.pullbackIndividualPayload_earliest (π : CountableRule (Seed × T)) (i : ℕ)
    (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i)
    (v : CompleteWorld (Seed × U)) (k : ℕ) :
    FirstAcceptance.Earliest (π.pullbackIndividualPayload i F t0).codeAccepted codeTime v k ↔
      FirstAcceptance.Earliest π.codeAccepted codeTime (recoverIndividualPayloadWorld i F v) k := by
  simp only [FirstAcceptance.Earliest,CountableRule.pullbackIndividualPayload_codeAccepted π i F t0 hBlind,
    codeTime_recoverIndividualPayload]

lemma CountableRule.pullbackIndividualPayload_hasFirst (π : CountableRule (Seed × T)) (i : ℕ)
    (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i) (v : CompleteWorld (Seed × U)) :
    FirstAcceptance.HasFirstIfAccepted (π.pullbackIndividualPayload i F t0).codeAccepted codeTime v ↔
      FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime (recoverIndividualPayloadWorld i F v) := by
  simp only [FirstAcceptance.HasFirstIfAccepted,CountableRule.pullbackIndividualPayload_codeAccepted π i F t0 hBlind,
    CountableRule.pullbackIndividualPayload_earliest π i F t0 hBlind]

lemma CountableRule.pullbackIndividualPayload_selectedCode (π : CountableRule (Seed × T)) (i : ℕ)
    (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i) (v : CompleteWorld (Seed × U)) :
    FirstAcceptance.selectedCode (π.pullbackIndividualPayload i F t0).codeAccepted codeTime v=
      FirstAcceptance.selectedCode π.codeAccepted codeTime (recoverIndividualPayloadWorld i F v) := by
  exact FirstAcceptance.selectedCode_timeScale (h := 1) zero_lt_one
    (fun k => π.pullbackIndividualPayload_codeAccepted i F t0 hBlind v k)
    (fun k _ => by simpa only [one_mul] using (codeTime_recoverIndividualPayload i F v k).symm)

lemma CountableRule.pullbackIndividualPayload_duration (π : CountableRule (Seed × T)) (i : ℕ)
    (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i) (v : CompleteWorld (Seed × U)) :
    (π.pullbackIndividualPayload i F t0).realizedDuration v=π.realizedDuration (recoverIndividualPayloadWorld i F v) := by
  simp only [CountableRule.realizedDuration,FirstAcceptance.stoppingTime,
    CountableRule.pullbackIndividualPayload_selectedCode π i F t0 hBlind,codeTime_recoverIndividualPayload]

lemma CountableRule.pullbackIndividualPayload_reward (π : CountableRule (Seed × T)) (i : ℕ)
    (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i) (a : ℝ) (v : CompleteWorld (Seed × U)) :
    π.realizedReward a (recoverIndividualPayloadWorld i F v)=
      (π.pullbackIndividualPayload i F t0).realizedReward a v+
        (π.pullbackIndividualPayload i F t0).individualSelectionIndicator i v*((F (v.2.1 i,v.2.2.2.2)).1-v.2.1 i) := by
  rw [CountableRule.individualSelectionIndicator_eq_code]
  unfold CountableRule.realizedReward FirstAcceptance.reward
  rw [CountableRule.pullbackIndividualPayload_selectedCode π i F t0 hBlind]
  cases hs : FirstAcceptance.selectedCode π.codeAccepted codeTime (recoverIndividualPayloadWorld i F v) with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one,codeValue_recoverIndividualPayload,Nat.add_right_cancel_iff]
    by_cases hk : k=candidateEnumeration (Sum.inl i)
    · subst k
      simp [codeValue,individual_candidate_point]
    · simp [hk]

end ProphetSecretary.Limiting.CountableInstance
