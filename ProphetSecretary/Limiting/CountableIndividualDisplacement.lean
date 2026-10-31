import ProphetSecretary.Limiting.CountableDisplayedIndividualPolicy
import ProphetSecretary.Limiting.CountableIndividualScore

/-!
# Scalar payoffs for a displayed individual value

The displacement is counted only if that individual is selected. Both
observable policy simulations preserve duration and give the same exact
scalar displacement, even for a noninjective measurable display map.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedCountablePolicy
variable {B : CountableInstance}

noncomputable def individualDisplacementMean (π : RandomizedCountablePolicy B) (i : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∫ v, π.rule.individualSelectionIndicator i v*(g (v.2.1 i)-v.2.1 i) ∂B.completeWorldLaw π.seedLaw

lemma integrable_individualDisplacement (π : RandomizedCountablePolicy B) (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap) :
    Integrable (fun v => π.rule.individualSelectionIndicator i v*(g (v.2.1 i)-v.2.1 i)) (B.completeWorldLaw π.seedLaw) := by
  have hXi := B.individualValue_completeWorld_measurePreserving π.seedLaw i
  have hm : Measurable (fun v : CompleteWorld π.Seed => g (v.2.1 i)-v.2.1 i) :=
    (hg.comp hXi.measurable).sub hXi.measurable
  apply (π.rule.integrable_individualSelectionIndicator π.measurable_rule B π.seedLaw i).mul_bdd hm.aestronglyMeasurable
  filter_upwards [hXi.quasiMeasurePreserving.ae hSupport,hXi.quasiMeasurePreserving.ae (B.individual_supported i)] with v hv hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith only [hv.1,hx.2],by linarith only [hv.2,hx.1]⟩

lemma exists_displayedIndividualPolicy_scalarObjective (π : RandomizedCountablePolicy B) (i : ℕ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap) (w c : ℝ) :
    ∃ policy : RandomizedCountablePolicy (B.mapIndividual i g hg hSupport),
      policy.scalarObjective w c=π.scalarObjective w c+w*π.individualDisplacementMean i g := by
  obtain ⟨policy,hT,hR⟩ := π.exists_displayedIndividualPolicy i g hg hSupport
  refine ⟨policy,?_⟩
  rw [integral_add π.integrable_reward (π.integrable_individualDisplacement i g hg hSupport)] at hR
  change w*policy.expectedReward+c*policy.expectedDuration=_
  rw [hR,hT]
  change w*(π.expectedReward+π.individualDisplacementMean i g)+c*π.expectedDuration=
    π.scalarObjective w c+w*π.individualDisplacementMean i g
  unfold scalarObjective
  ring

lemma singleIndividualPullback_expectedReward (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividual i g hg hSupport)) :
    policy.expectedReward=(policy.singleIndividualPullback i g hg hSupport).expectedReward+
      (policy.singleIndividualPullback i g hg hSupport).individualDisplacementMean i g := by
  let π := policy.singleIndividualPullback i g hg hSupport
  have hMP := B.mapSingleIndividualWorld_measurePreserving i g hg hSupport policy.seedLaw
  have hMean := hMP.hasLaw.integral_comp (policy.rule.measurable_realizedReward policy.measurable_rule B.terminal).aestronglyMeasurable
  change (∫ v, policy.rule.realizedReward B.terminal (mapSingleIndividualWorld i g v) ∂B.completeWorldLaw policy.seedLaw)=policy.expectedReward at hMean
  rw [← hMean]
  change _=(∫ v, π.rule.realizedReward B.terminal v ∂B.completeWorldLaw π.seedLaw)+π.individualDisplacementMean i g
  unfold individualDisplacementMean
  rw [← integral_add π.integrable_reward (π.integrable_individualDisplacement i g hg hSupport)]
  apply integral_congr_ae
  exact Eventually.of_forall (policy.rule.pullbackSingleIndividual_reward i g B.terminal)

lemma singleIndividualPullback_scalarObjective (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividual i g hg hSupport)) (w c : ℝ) :
    policy.scalarObjective w c=(policy.singleIndividualPullback i g hg hSupport).scalarObjective w c+
      w*(policy.singleIndividualPullback i g hg hSupport).individualDisplacementMean i g := by
  have hR := policy.singleIndividualPullback_expectedReward i g hg hSupport
  have hT := policy.singleIndividualPullback_expectedDuration i g hg hSupport
  unfold scalarObjective
  rw [hR,← hT]
  ring

end RandomizedCountablePolicy

lemma CountableInstance.optimalScalarValue_mapIndividual_eq_sSup (B : CountableInstance) (i : ℕ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap) (w c : ℝ) :
    (B.mapIndividual i g hg hSupport).optimalScalarValue w c=
      sSup (Set.range (fun π : RandomizedCountablePolicy B => π.scalarObjective w c+w*π.individualDisplacementMean i g)) := by
  let D := B.mapIndividual i g hg hSupport
  let J := fun π : RandomizedCountablePolicy B => π.scalarObjective w c+w*π.individualDisplacementMean i g
  have hUpper (π : RandomizedCountablePolicy B) : J π≤D.optimalScalarValue w c := by
    obtain ⟨policy,hJ⟩ := π.exists_displayedIndividualPolicy_scalarObjective i g hg hSupport w c
    exact hJ.symm.trans_le (D.scalarObjective_le_value policy w c)
  have hBound : BddAbove (Set.range J) := ⟨D.optimalScalarValue w c,by rintro _ ⟨π,rfl⟩; exact hUpper π⟩
  apply le_antisymm
  · apply csSup_le (D.scalarPayoffs_nonempty w c)
    rintro _ ⟨policy,rfl⟩
    have h := policy.singleIndividualPullback_scalarObjective i g hg hSupport w c
    exact h.trans_le (le_csSup hBound (Set.mem_range_self _))
  · exact csSup_le ⟨_,⟨RandomizedCountablePolicy.waiting B,rfl⟩⟩ (by rintro _ ⟨π,rfl⟩; exact hUpper π)

end ProphetSecretary.Limiting
