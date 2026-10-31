import ProphetSecretary.Limiting.TaggedHybridAmplitude
import ProphetSecretary.Limiting.HybridPoissonPayloadInstance
import ProphetSecretary.Limiting.PoissonConditionalPayloadLaw
import ProphetSecretary.Limiting.PoissonPayloadHybridGraph
import ProphetSecretary.Limiting.TaggedHybridForwardRecovery

/-!
# Actual common-policy simulations for displayed Poisson marks

The conditional sampler is constructed from the displayed intensity. Its
independent chronological uniforms reconstruct exactly the old tagged
experiment, and the selected reward identity gives the payoff displacement.
Policy seeds are arbitrary measurable probability spaces throughout.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal unitInterval

namespace ProphetSecretary.Limiting

noncomputable def RandomizedTaggedHybridPolicy.payloadDisplacementMean {n : ℕ} {T : Type}
    [MeasurableSpace T] (π : RandomizedTaggedHybridPolicy n T) (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) (t0 : T) (g : ℝ × T → ℝ) : ℝ :=
  ∫ v, π.rule.payloadSelectedAmplitude t0 (fun z => g z-z.1) v ∂taggedHybridWorldLaw B π.seedLaw κ

private theorem reconstruct_mean_transport {n : ℕ} {T : Type} [MeasurableSpace T]
    (π : RandomizedTaggedHybridPolicy n T) (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (H : ℝ≥0) (hH : B.cap≤H)
    (g : ℝ × T → ℝ) (hg : Measurable g)
    (hImage : ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, g z∈Ioc (0 : ℝ) H)
    {K : ℝ} (hK : 0≤K) (hDisplacement : ∀ z, |g z-z.1|≤K)
    (F : ℝ × unitInterval → ℝ × T) (hF : Measurable F)
    (hGraph : ∀ᵐ z ∂(displayedPayloadMarkLaw B.intensity κ g hg : Measure ℝ).prod (volume : Measure unitInterval), g (F z)=z.1)
    (hLaw : MeasurePreserving (conditionalTaggedHybridWorld F)
      ((B.displayPoissonPayload H hH κ g hg hImage).law
        (π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval)))))
      (taggedHybridWorldLaw B π.seedLaw κ)) :
    let policy := π.reconstructPolicy (volume : Measure unitInterval) F hF
    policy.expectedReward (B.displayPoissonPayload H hH κ g hg hImage)=
      (π.sampleTags κ).expectedReward B+π.payloadDisplacementMean B κ t0 g ∧
    policy.expectedDuration (B.displayPoissonPayload H hH κ g hg hImage)=(π.sampleTags κ).expectedDuration B := by
  let D := B.displayPoissonPayload H hH κ g hg hImage
  let Q := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))
  let δ := fun z : ℝ × T => g z-z.1
  let Obs := fun v : PayloadConfiguration T × Model.World n π.Seed =>
    π.rule.payloadReward t0 v+π.rule.payloadSelectedAmplitude t0 δ v
  have hδ : Measurable δ := hg.sub measurable_fst
  have hObs : Measurable Obs := (π.rule.measurable_payloadReward π.measurable_rule t0).add
    (π.rule.measurable_payloadSelectedAmplitude π.measurable_rule t0 δ hδ)
  have hRInt := π.rule.integrable_payloadReward π.measurable_rule B π.seedLaw κ t0
  have hAInt := π.rule.integrable_payloadSelectedAmplitude π.measurable_rule B π.seedLaw κ t0 δ hδ hK hDisplacement
  have hMeanR := hLaw.hasLaw.integral_comp hObs.aestronglyMeasurable
  have hMeanT := hLaw.hasLaw.integral_comp (π.rule.measurable_payloadDuration π.measurable_rule t0).aestronglyMeasurable
  have hCfg : MeasurePreserving (Prod.fst : HybridWorld n (π.Seed × (ℕ → unitInterval)) → Configuration)
      (D.law (π.seedLaw.prod Q)) (configurationLaw D.intensity) := measurePreserving_fst
  have hClock := hCfg.quasiMeasurePreserving.ae (configuration_times_distinct D.intensity)
  have hG := hybrid_chronological_payload_graph_ae B.individuals B.intensity π.seedLaw
    (volume : Measure unitInterval) κ F hF g hg hGraph
  have hRAE : ∀ᵐ v : HybridWorld n (π.Seed × (ℕ → unitInterval)) ∂D.law (π.seedLaw.prod Q),
      (π.rule.reconstructPayload F).realizedReward 0 v=Obs (conditionalTaggedHybridWorld F v) := by
    filter_upwards [hClock,hG] with v hv hgv
    have hDisplay (j : Fin v.1.1) : (v.1.2 j).2=
        ((chronologicalPayloadConfiguration F (v.1,v.2.2.2.2)).2 j).2.1+
          (1 : ℝ)*δ ((chronologicalPayloadConfiguration F (v.1,v.2.2.2.2)).2 j).2 := by
      change (v.1.2 j).2=(F ((v.1.2 j).2,v.2.2.2.2
        (Model.Instance.arrivalRank (fun k : Fin v.1.1 => (v.1.2 k).1) j).val)).1+
        1*(g (F ((v.1.2 j).2,v.2.2.2.2
          (Model.Instance.arrivalRank (fun k : Fin v.1.1 => (v.1.2 k).1) j).val))-
          (F ((v.1.2 j).2,v.2.2.2.2 (Model.Instance.arrivalRank (fun k : Fin v.1.1 => (v.1.2 k).1) j).val)).1)
      rw [one_mul,hgv j]
      ring
    have h := π.rule.reconstructPayload_reward t0 v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 F hF hv δ 1 hDisplay
    dsimp only [HybridRule.realizedReward,Obs,conditionalTaggedHybridWorld]
    simpa only [one_mul] using h
  have hTAE : ∀ᵐ v : HybridWorld n (π.Seed × (ℕ → unitInterval)) ∂D.law (π.seedLaw.prod Q),
      (π.rule.reconstructPayload F).realizedDuration v=π.rule.payloadDuration t0 (conditionalTaggedHybridWorld F v) := by
    filter_upwards [hClock] with v hv
    exact π.rule.reconstructPayload_duration t0 v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 F hF hv
  have hOldR : (∫ v, π.rule.payloadReward t0 v ∂taggedHybridWorldLaw B π.seedLaw κ)=(π.sampleTags κ).expectedReward B := by
    change _=∫ v, π.rule.sampleTags.realizedReward B.terminal v
      ∂B.law (π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => κ)))
    rw [hZero]
    simp only [NNReal.coe_zero]
    exact π.rule.integral_payloadReward_eq π.measurable_rule B π.seedLaw κ t0
  constructor
  · change (∫ v : HybridWorld n (π.Seed × (ℕ → unitInterval)), (π.rule.reconstructPayload F).realizedReward D.terminal v
      ∂D.law (π.seedLaw.prod Q))=_
    have hDZero : D.terminal=0 := hZero
    rw [hDZero]
    simp only [NNReal.coe_zero]
    calc
      _ = ∫ v, Obs (conditionalTaggedHybridWorld F v) ∂D.law (π.seedLaw.prod Q) := integral_congr_ae hRAE
      _ = ∫ v, Obs v ∂taggedHybridWorldLaw B π.seedLaw κ := hMeanR
      _ = (∫ v, π.rule.payloadReward t0 v ∂taggedHybridWorldLaw B π.seedLaw κ)+
          ∫ v, π.rule.payloadSelectedAmplitude t0 δ v ∂taggedHybridWorldLaw B π.seedLaw κ := integral_add hRInt hAInt
      _ = _ := by rw [hOldR]; rfl
  · change (∫ v : HybridWorld n (π.Seed × (ℕ → unitInterval)), (π.rule.reconstructPayload F).realizedDuration v
      ∂D.law (π.seedLaw.prod Q))=_
    calc
      _ = ∫ v, π.rule.payloadDuration t0 (conditionalTaggedHybridWorld F v) ∂D.law (π.seedLaw.prod Q) := integral_congr_ae hTAE
      _ = ∫ v, π.rule.payloadDuration t0 v ∂taggedHybridWorldLaw B π.seedLaw κ := hMeanT
      _ = _ := π.rule.integral_payloadDuration_eq π.measurable_rule B π.seedLaw κ t0

/-- A genuine ordinary displayed-law policy realizes every fixed tagged-policy
payoff, with the exact selected anonymous displacement and unchanged duration. -/
theorem RandomizedTaggedHybridPolicy.exists_displayedPolicy_means {n : ℕ} {T : Type}
    [MeasurableSpace T] [StandardBorelSpace T] (π : RandomizedTaggedHybridPolicy n T)
    (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (H : ℝ≥0) (hH : B.cap≤H)
    (g : ℝ × T → ℝ) (hg : Measurable g)
    (hImage : ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, g z∈Ioc (0 : ℝ) H)
    {K : ℝ} (hK : 0≤K) (hDisplacement : ∀ z, |g z-z.1|≤K) :
    ∃ policy : RandomizedHybridPolicy n,
      policy.expectedReward (B.displayPoissonPayload H hH κ g hg hImage)=
        (π.sampleTags κ).expectedReward B+π.payloadDisplacementMean B κ t0 g ∧
      policy.expectedDuration (B.displayPoissonPayload H hH κ g hg hImage)=(π.sampleTags κ).expectedDuration B := by
  obtain ⟨F,hF,hGraph,hLaw⟩ := exists_poisson_conditional_payload_sampler B.intensity κ g hg
  refine ⟨π.reconstructPolicy (volume : Measure unitInterval) F hF,?_⟩
  exact reconstruct_mean_transport π B hZero κ t0 H hH g hg hImage hK hDisplacement F hF hGraph (hLaw n B.individuals π.seedLaw)

private theorem recovered_display_scalar {n : ℕ} {T : Type} [MeasurableSpace T]
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (H : ℝ≥0) (hH : B.cap≤H)
    (g : ℝ × T → ℝ) (hg : Measurable g)
    (hImage : ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, g z∈Ioc (0 : ℝ) H)
    (F : ℝ × unitInterval → ℝ × T) (hF : Measurable F)
    (hGraph : ∀ᵐ z ∂(displayedPayloadMarkLaw B.intensity κ g hg : Measure ℝ).prod (volume : Measure unitInterval), g (F z)=z.1)
    (w c : ℝ) :
    (((π.observePayload g hg).reconstructPolicy (volume : Measure unitInterval) F hF).scalarObjective
      (B.displayPoissonPayload H hH κ g hg hImage) w c)=
      π.scalarObjective (B.displayPoissonPayload H hH κ g hg hImage) w c := by
  let D := B.displayPoissonPayload H hH κ g hg hImage
  let Q := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))
  let U := fun v : HybridWorld n π.Seed => w*π.rule.realizedReward D.terminal v+c*π.rule.realizedDuration v
  have hU : Measurable U := ((π.rule.measurable_realizedReward π.measurable_rule D.terminal).const_mul w).add
    ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have hDrop : MeasurePreserving (fun v : HybridWorld n (π.Seed × (ℕ → unitInterval)) =>
      (v.1,(v.2.1,(v.2.2.1,v.2.2.2.1)))) (D.law (π.seedLaw.prod Q)) (D.law π.seedLaw) :=
    (MeasurePreserving.id (configurationLaw D.intensity)).prod
      ((MeasurePreserving.id D.individuals.valuesLaw).prod
        ((MeasurePreserving.id (Model.Instance.clocksLaw n)).prod measurePreserving_fst))
  have hMean := hDrop.hasLaw.integral_comp hU.aestronglyMeasurable
  have hCfg : MeasurePreserving (Prod.fst : HybridWorld n (π.Seed × (ℕ → unitInterval)) → Configuration)
      (D.law (π.seedLaw.prod Q)) (configurationLaw D.intensity) := measurePreserving_fst
  have hClock := hCfg.quasiMeasurePreserving.ae (configuration_times_distinct D.intensity)
  have hG := hybrid_chronological_payload_graph_ae B.individuals B.intensity π.seedLaw
    (volume : Measure unitInterval) κ F hF g hg hGraph
  change (∫ v : HybridWorld n (π.Seed × (ℕ → unitInterval)),
    w*((π.rule.observePayload g).reconstructPayload F).realizedReward D.terminal v+
      c*((π.rule.observePayload g).reconstructPayload F).realizedDuration v ∂D.law (π.seedLaw.prod Q))=∫ v, U v ∂D.law π.seedLaw
  rw [← hMean]
  apply integral_congr_ae
  filter_upwards [hClock,hG] with v hv hgv
  have h := π.rule.observePayload_reconstruct_outcomes v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 F hF g hg hv hgv
  have hDZero : D.terminal=0 := hZero
  rw [hDZero]
  simp only [NNReal.coe_zero]
  dsimp only [U,HybridRule.realizedReward,HybridRule.realizedDuration]
  rw [hDZero]
  simp only [NNReal.coe_zero]
  exact congrArg₂ (fun a b : ℝ => w*a+c*b) h.1 h.2

/-- The actual full displayed-policy value is a common supremum over policies
observing old anonymous payloads only at their current and past occurrences. -/
theorem FiniteIntensityHybridInstance.optimalScalarValue_displayPoissonPayload_eq_sSup
    {n : ℕ} {T : Type} [MeasurableSpace T] [StandardBorelSpace T]
    (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (H : ℝ≥0) (hH : B.cap≤H)
    (g : ℝ × T → ℝ) (hg : Measurable g)
    (hImage : ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, g z∈Ioc (0 : ℝ) H)
    {K : ℝ} (hK : 0≤K) (hDisplacement : ∀ z, |g z-z.1|≤K) (w c : ℝ) :
    (B.displayPoissonPayload H hH κ g hg hImage).optimalScalarValue w c=
      sSup (Set.range (fun π : RandomizedTaggedHybridPolicy n T =>
        (π.sampleTags κ).scalarObjective B w c+w*π.payloadDisplacementMean B κ t0 g)) := by
  let D := B.displayPoissonPayload H hH κ g hg hImage
  let J := fun π : RandomizedTaggedHybridPolicy n T =>
    (π.sampleTags κ).scalarObjective B w c+w*π.payloadDisplacementMean B κ t0 g
  obtain ⟨F,hF,hGraph,hLaw⟩ := exists_poisson_conditional_payload_sampler B.intensity κ g hg
  have hLower (π : RandomizedTaggedHybridPolicy n T) :
      (π.reconstructPolicy (volume : Measure unitInterval) F hF).scalarObjective D w c=J π := by
    have hMeans := reconstruct_mean_transport π B hZero κ t0 H hH g hg hImage hK hDisplacement F hF hGraph
      (hLaw n B.individuals π.seedLaw)
    dsimp only [J]
    rw [RandomizedHybridPolicy.scalarObjective_eq,RandomizedHybridPolicy.scalarObjective_eq,hMeans.1,hMeans.2]
    ring
  have hBound (π : RandomizedTaggedHybridPolicy n T) : J π≤D.optimalScalarValue w c :=
    (hLower π).symm.trans_le (D.scalarObjective_le_value _ w c)
  have hBdd : BddAbove (Set.range J) := ⟨D.optimalScalarValue w c,by rintro _ ⟨π,rfl⟩; exact hBound π⟩
  apply le_antisymm
  · apply csSup_le (D.scalarPayoffs_nonempty w c)
    rintro _ ⟨π,rfl⟩
    have hRecovery := recovered_display_scalar π B hZero κ H hH g hg hImage F hF hGraph w c
    have hEq : π.scalarObjective D w c=J (π.observePayload g hg) := hRecovery.symm.trans (hLower (π.observePayload g hg))
    exact hEq.trans_le (le_csSup hBdd (Set.mem_range_self _))
  · exact csSup_le ⟨_,⟨(RandomizedHybridPolicy.waiting n).observePayload g hg,rfl⟩⟩
      (by rintro _ ⟨π,rfl⟩; exact hBound π)

end ProphetSecretary.Limiting

