import ProphetSecretary.Limiting.CountableSingleIndividualPullback
import ProphetSecretary.Limiting.CountableSingleValueReward
import Mathlib.Probability.HasLaw

/-!
# Policy transport under a measurable individual-value map

Every mapped-instance policy pulls back to a policy with the original
observations and independent seed. The executed selected occurrence and
duration are identical on mapped worlds. Reward differs only by the mapped
candidate's value change on its selection event.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance
variable {Seed : Type*}

lemma CountableRule.pullbackSingleIndividual_reward (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (a : ℝ) (v : CompleteWorld Seed) :
    π.realizedReward a (mapSingleIndividualWorld i g v)=
      (π.pullbackSingleIndividual i g).realizedReward a v+
        (π.pullbackSingleIndividual i g).individualSelectionIndicator i v*(g (v.2.1 i)-v.2.1 i) := by
  rw [CountableRule.individualSelectionIndicator_eq_code]
  unfold CountableRule.realizedReward FirstAcceptance.reward
  rw [CountableRule.pullbackSingleIndividual_selectedCode]
  cases hs : FirstAcceptance.selectedCode π.codeAccepted codeTime (mapSingleIndividualWorld i g v) with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one,mapSingleIndividualWorld,
      codeValue_replaceIndividualValue,Nat.add_right_cancel_iff]
    by_cases hk : k=candidateEnumeration (Sum.inl i)
    · subst k
      simp [codeValue,individual_candidate_point]
    · simp [hk]

end CountableInstance

namespace RandomizedCountablePolicy
variable {B : CountableInstance}

noncomputable def singleIndividualPullback (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x ∈ Icc (0 : ℝ) B.cap)
    (π : RandomizedCountablePolicy (B.mapIndividual i g hg hSupport)) : RandomizedCountablePolicy B where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.pullbackSingleIndividual i g
  measurable_rule := π.rule.pullbackSingleIndividual_isMeasurable π.measurable_rule i hg
  admissible := by
    have hMP := B.mapSingleIndividualWorld_measurePreserving i g hg hSupport π.seedLaw
    filter_upwards [hMP.quasiMeasurePreserving.ae π.admissible] with v hv
    exact (π.rule.pullbackSingleIndividual_hasFirst i g v).mpr hv

theorem singleIndividualPullback_expectedDuration (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x ∈ Icc (0 : ℝ) B.cap)
    (π : RandomizedCountablePolicy (B.mapIndividual i g hg hSupport)) :
    (singleIndividualPullback i g hg hSupport π).expectedDuration=π.expectedDuration := by
  have hMP := B.mapSingleIndividualWorld_measurePreserving i g hg hSupport π.seedLaw
  have hMean := hMP.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  change (∫ v, (π.rule.pullbackSingleIndividual i g).realizedDuration v ∂B.completeWorldLaw π.seedLaw)=
    ∫ v, π.rule.realizedDuration v ∂(B.mapIndividual i g hg hSupport).completeWorldLaw π.seedLaw
  rw [← hMean]
  apply integral_congr_ae
  exact Eventually.of_forall (π.rule.pullbackSingleIndividual_duration i g)

end RandomizedCountablePolicy
end ProphetSecretary.Limiting
