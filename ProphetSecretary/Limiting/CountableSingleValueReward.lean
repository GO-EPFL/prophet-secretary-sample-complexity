import ProphetSecretary.Limiting.CountableConditionalSelection

/-!
# Reward when one value changes but the selected occurrence does not

All candidate identities and clocks are preserved. The reward change is the
candidate's value change times its actual selection indicator, including
the zero reward or terminal reward convention when no occurrence is selected.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma codeValue_replaceIndividualValue (i : ℕ) (v : CompleteWorld Seed) (x : ℝ) (k : ℕ) :
    codeValue (replaceIndividualValue i (v,x)) k=
      if k=candidateEnumeration (Sum.inl i) then x else codeValue v k := by
  by_cases hk : k=candidateEnumeration (Sum.inl i)
  · subst k
    simp [codeValue,individual_candidate_point,replaceIndividualValue]
  · have hc : candidateEnumeration.symm k ≠ Sum.inl i := by
      intro h
      exact hk (by simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration h)
    rw [if_neg hk]
    exact congrArg Prod.snd (candidatePoint_replaceIndividualValue_of_ne i (v,x) _ hc)

lemma CountableRule.individualSelectionIndicator_eq_code (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) : π.individualSelectionIndicator i v=
      if FirstAcceptance.selectedCode π.codeAccepted codeTime v=candidateEnumeration (Sum.inl i)+1 then 1 else 0 := by
  unfold CountableRule.individualSelectionIndicator CountableRule.SelectsIndividual
  rw [← FirstAcceptance.selectedCode_eq_succ_iff]
  split_ifs <;> rfl

lemma CountableRule.reward_replaceIndividualValue_eq_of_selectedCode_eq (π : CountableRule Seed)
    (a : ℝ) (i : ℕ) (v : CompleteWorld Seed) (x : ℝ)
    (hCode : FirstAcceptance.selectedCode π.codeAccepted codeTime (replaceIndividualValue i (v,x))=
      FirstAcceptance.selectedCode π.codeAccepted codeTime v) :
    π.realizedReward a (replaceIndividualValue i (v,x))=
      π.realizedReward a v+π.individualSelectionIndicator i v*(x-v.2.1 i) := by
  rw [CountableRule.individualSelectionIndicator_eq_code]
  unfold CountableRule.realizedReward FirstAcceptance.reward
  rw [hCode]
  cases hs : FirstAcceptance.selectedCode π.codeAccepted codeTime v with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one,codeValue_replaceIndividualValue,Nat.add_right_cancel_iff]
    by_cases hk : k=candidateEnumeration (Sum.inl i)
    · subst k
      simp [codeValue,individual_candidate_point]
    · simp [hk]

end ProphetSecretary.Limiting.CountableInstance
