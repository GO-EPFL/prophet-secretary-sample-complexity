import ProphetSecretary.Limiting.CountableIndividualMean
import ProphetSecretary.Limiting.CountableSingleIndividualTransport
import ProphetSecretary.Limiting.CountableMeanRewardPreservation

/-!
# Simulating any mean-contracted policy on the original instance

The simulator substitutes the mean only in the candidate's current value and
observed history. Its selection ignores the original value. Actual product
independence therefore preserves expected reward, and the causal pullback
preserves expected duration. The competing policy is otherwise unrestricted.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance
namespace RandomizedCountablePolicy
variable {B : CountableInstance}

noncomputable def meanIndividualPullback (i : ℕ) (π : RandomizedCountablePolicy (B.contractIndividual i)) :
    RandomizedCountablePolicy B :=
  singleIndividualPullback i (fun _ => B.individualMean i) measurable_const
    (Eventually.of_forall (fun _ => B.individualMean_mem_cap i)) π

theorem meanIndividualPullback_expectedDuration (i : ℕ)
    (π : RandomizedCountablePolicy (B.contractIndividual i)) :
    (meanIndividualPullback i π).expectedDuration=π.expectedDuration :=
  singleIndividualPullback_expectedDuration i (fun _ => B.individualMean i) measurable_const
    (Eventually.of_forall (fun _ => B.individualMean_mem_cap i)) π

theorem meanIndividualPullback_expectedReward (i : ℕ)
    (π : RandomizedCountablePolicy (B.contractIndividual i)) :
    (meanIndividualPullback i π).expectedReward=π.expectedReward := by
  let m := B.individualMean i
  let ρ : CountableRule π.Seed := π.rule.pullbackSingleIndividual i (fun _ => m)
  have hρ : ρ.IsMeasurable := π.rule.pullbackSingleIndividual_isMeasurable π.measurable_rule i measurable_const
  have hIdempotent (v : CompleteWorld π.Seed) :
      mapSingleIndividualWorld i (fun _ => m) (replaceIndividualValue i (v,m))=replaceIndividualValue i (v,m) := by
    simp only [mapSingleIndividualWorld,replaceIndividualValue,Function.update_idem]
  have hCode (v : CompleteWorld π.Seed) :
      FirstAcceptance.selectedCode ρ.codeAccepted codeTime (replaceIndividualValue i (v,m))=
        FirstAcceptance.selectedCode ρ.codeAccepted codeTime v := by
    change FirstAcceptance.selectedCode (π.rule.pullbackSingleIndividual i (fun _ => m)).codeAccepted codeTime _=
      FirstAcceptance.selectedCode (π.rule.pullbackSingleIndividual i (fun _ => m)).codeAccepted codeTime _
    rw [CountableRule.pullbackSingleIndividual_selectedCode,CountableRule.pullbackSingleIndividual_selectedCode]
    exact congrArg (FirstAcceptance.selectedCode π.rule.codeAccepted codeTime) (hIdempotent v)
  have hPreserve := ρ.integral_reward_mean_substitution_eq hρ B π.seedLaw i
    (Eventually.of_forall hCode)
  have hReward (v : CompleteWorld π.Seed) :
      ρ.realizedReward B.terminal (replaceIndividualValue i (v,m))=
        π.rule.realizedReward B.terminal (replaceIndividualValue i (v,m)) := by
    change (π.rule.pullbackSingleIndividual i (fun _ => m)).realizedReward _ _=_
    unfold CountableRule.realizedReward FirstAcceptance.reward
    rw [CountableRule.pullbackSingleIndividual_selectedCode,hIdempotent v]
  have hMP := B.meanSubstitution_measurePreserving i π.seedLaw
  have hMean := hMP.hasLaw.integral_comp (π.rule.measurable_realizedReward π.measurable_rule B.terminal).aestronglyMeasurable
  calc
    (meanIndividualPullback i π).expectedReward = ∫ v, ρ.realizedReward B.terminal (replaceIndividualValue i (v,m)) ∂B.completeWorldLaw π.seedLaw :=
      hPreserve.symm
    _ = ∫ v, π.rule.realizedReward B.terminal (replaceIndividualValue i (v,m)) ∂B.completeWorldLaw π.seedLaw :=
      integral_congr_ae (Eventually.of_forall hReward)
    _ = π.expectedReward := hMean

theorem meanIndividualPullback_scalarObjective (i : ℕ)
    (π : RandomizedCountablePolicy (B.contractIndividual i)) (w c : ℝ) :
    (meanIndividualPullback i π).scalarObjective w c=π.scalarObjective w c := by
  rw [scalarObjective,scalarObjective,meanIndividualPullback_expectedReward,meanIndividualPullback_expectedDuration]

end RandomizedCountablePolicy
namespace CountableInstance

theorem contractIndividual_value_le (B : CountableInstance) (i : ℕ) (w c : ℝ) :
    (B.contractIndividual i).optimalScalarValue w c ≤ B.optimalScalarValue w c := by
  apply csSup_le ((B.contractIndividual i).scalarPayoffs_nonempty w c)
  rintro _ ⟨π,rfl⟩
  change π.scalarObjective w c ≤ B.optimalScalarValue w c
  rw [← RandomizedCountablePolicy.meanIndividualPullback_scalarObjective i π w c]
  exact B.scalarObjective_le_value _ w c

end CountableInstance
end ProphetSecretary.Limiting
