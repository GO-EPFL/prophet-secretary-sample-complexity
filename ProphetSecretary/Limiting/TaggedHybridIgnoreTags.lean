import ProphetSecretary.Limiting.TaggedHybridDisplayRule
import ProphetSecretary.Limiting.TaggedHybridPrefixExecution
import ProphetSecretary.Limiting.ChronologicalConditionalHistory

/-!
# Tag-ignoring hybrid policies preserve the original experiment

Every ordinary hybrid policy is a member of the tagged observation class by
forgetting current and past tags. The exact actual action/mean identities
hold for every retained law and finite intensity, including zero intensity.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed T : Type*} [MeasurableSpace T]

lemma HybridRule.observePayload_fst_actions (π : HybridRule n Seed) (r : Seed)
    (σ : ℕ → T) (x u : Fin n → ℝ) (ω : Configuration) (k : Fin (n+ω.1)) :
    (((π.observePayload (Prod.fst : ℝ × T → ℝ)).sampleTags).asFinitePolicy ω.1).action
      (r,σ) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k=
      (π.asFinitePolicy ω.1).action r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [HybridRule.individual_action,HybridRule.individual_action]
    change π.individual r (u i) i (x i) (Model.history Finset.univ x u (u i))
      ((chronologicalTaggedHistory σ (observedFiniteHistory ω (u i))).map forgetPayloadPoint)=_
    rw [forget_chronologicalTaggedHistory,observedFiniteHistory_coe]
    rfl
  · rw [HybridRule.poisson_action,HybridRule.poisson_action]
    change π.poisson r (ω.2 j).1 (ω.2 j).2 (Model.history Finset.univ x u (ω.2 j).1)
      ((chronologicalTaggedHistory σ (observedFiniteHistory ω (ω.2 j).1)).map forgetPayloadPoint)=_
    rw [forget_chronologicalTaggedHistory,observedFiniteHistory_coe]
    rfl

lemma HybridRule.observePayload_fst_outcomes (π : HybridRule n Seed) (r : Seed)
    (σ : ℕ → T) (x u : Fin n → ℝ) (ω : Configuration) :
    (π.observePayload (Prod.fst : ℝ × T → ℝ)).sampleTags.reward 0 (r,σ) x u ω=π.reward 0 r x u ω ∧
      (π.observePayload (Prod.fst : ℝ × T → ℝ)).sampleTags.stoppingTime (r,σ) x u ω=π.stoppingTime r x u ω := by
  have h := ((((π.observePayload (Prod.fst : ℝ × T → ℝ)).sampleTags).asFinitePolicy ω.1)).outcomes_eq_of_actions_eq
    (π.asFinitePolicy ω.1) (r,σ) r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2)
    (π.observePayload_fst_actions r σ x u ω)
  constructor
  · rw [HybridRule.reward_zero_eq_finite,HybridRule.reward_zero_eq_finite]
    exact h.1
  · exact h.2

lemma RandomizedHybridPolicy.observePayload_fst_scalarObjective {n : ℕ} {T : Type} [MeasurableSpace T]
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (w c : ℝ) :
    ((π.observePayload (Prod.fst : ℝ × T → ℝ) measurable_fst).sampleTags κ).scalarObjective B w c=π.scalarObjective B w c := by
  let K := Measure.infinitePi (fun _ : ℕ => κ)
  have hMP : MeasurePreserving (fun v : HybridWorld n (π.Seed × (ℕ → T)) =>
      (v.1,(v.2.1,(v.2.2.1,v.2.2.2.1)))) (B.law (π.seedLaw.prod K)) (B.law π.seedLaw) :=
    (MeasurePreserving.id (configurationLaw B.intensity)).prod
      ((MeasurePreserving.id B.individuals.valuesLaw).prod
        ((MeasurePreserving.id (Model.Instance.clocksLaw n)).prod measurePreserving_fst))
  have hRMean := hMP.hasLaw.integral_comp (π.rule.measurable_realizedReward π.measurable_rule 0).aestronglyMeasurable
  have hTMean := hMP.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  have hR : ((π.observePayload (Prod.fst : ℝ × T → ℝ) measurable_fst).sampleTags κ).expectedReward B=π.expectedReward B := by
    change (∫ v : HybridWorld n (π.Seed × (ℕ → T)),
      (π.rule.observePayload (Prod.fst : ℝ × T → ℝ)).sampleTags.realizedReward B.terminal v ∂B.law (π.seedLaw.prod K))=
        ∫ v, π.rule.realizedReward B.terminal v ∂B.law π.seedLaw
    rw [hZero]
    simp only [NNReal.coe_zero]
    rw [← hRMean]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (π.rule.observePayload_fst_outcomes v.2.2.2.1 v.2.2.2.2 v.2.1 v.2.2.1 v.1).1)
  have hT : ((π.observePayload (Prod.fst : ℝ × T → ℝ) measurable_fst).sampleTags κ).expectedDuration B=π.expectedDuration B := by
    change (∫ v : HybridWorld n (π.Seed × (ℕ → T)),
      (π.rule.observePayload (Prod.fst : ℝ × T → ℝ)).sampleTags.realizedDuration v ∂B.law (π.seedLaw.prod K))=
        ∫ v, π.rule.realizedDuration v ∂B.law π.seedLaw
    rw [← hTMean]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (π.rule.observePayload_fst_outcomes v.2.2.2.1 v.2.2.2.2 v.2.1 v.2.2.1 v.1).2)
  rw [RandomizedHybridPolicy.scalarObjective_eq,RandomizedHybridPolicy.scalarObjective_eq,hR,hT]

end ProphetSecretary.Limiting
