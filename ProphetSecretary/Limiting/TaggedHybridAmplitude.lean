import ProphetSecretary.Limiting.TaggedHybridPayloadOutcomes
import ProphetSecretary.Limiting.TaggedHybridPayloadLaw

/-!
# Measurable integrable selected amplitudes in the tagged experiment

At most one occurrence is selected, so the amplitude bound is independent of
the Poisson count and retained dimension. The actual base-world pushforward
also proves integrability of the intrinsic old reward.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed T : Type*} [MeasurableSpace Seed] [MeasurableSpace T]

instance taggedHybridWorldLaw_probability (B : FiniteIntensityHybridInstance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (κ : Measure T) [IsProbabilityMeasure κ] :
    IsProbabilityMeasure (taggedHybridWorldLaw B ν κ) := by
  unfold taggedHybridWorldLaw
  infer_instance

lemma TaggedHybridRule.measurable_payloadSelectedAmplitude (π : TaggedHybridRule n Seed T)
    (hπ : π.IsMeasurable) (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A) :
    Measurable (π.payloadSelectedAmplitude t0 A) := by
  apply ProphetSecretary.Probability.measurable_of_sigma_prod_branches
  intro N
  let Ω := (Fin N → ℝ × (ℝ × T)) × Model.World n Seed
  let oldPoints := fun z : Ω => fun j : Fin N => ((z.1 j).1,(z.1 j).2.1)
  have hRich : Measurable (fun z : Ω => payloadConfigurationMk N z.1) :=
    (measurable_payloadConfiguration_mk N).comp measurable_fst
  have hr : Measurable (fun z : Ω => (z.2.2.2,payloadTagSequence t0 (payloadConfigurationMk N z.1))) :=
    measurable_snd.snd.snd.prodMk ((measurable_payloadTagSequence t0).comp hRich)
  have hx (i : Fin n) : Measurable (fun z : Ω => z.2.1 i) := (measurable_pi_apply i).comp measurable_snd.fst
  have hu (i : Fin n) : Measurable (fun z : Ω => z.2.2.1 i) := (measurable_pi_apply i).comp measurable_snd.snd.fst
  have hv (j : Fin N) : Measurable (fun z : Ω => oldPoints z j) :=
    (((measurable_pi_apply j).comp measurable_fst).fst).prodMk (((measurable_pi_apply j).comp measurable_fst).snd.fst)
  have hX (k : Fin (n+N)) : Measurable (fun z : Ω => combinedValues z.2.1 (oldPoints z) k) :=
    measurable_combinedValues_family _ hx _ hv k
  have hU (k : Fin (n+N)) : Measurable (fun z : Ω => combinedClocks z.2.2.1 (oldPoints z) k) :=
    measurable_combinedClocks_family _ hu _ hv k
  have hTag (k : Fin (n+N)) : Measurable (fun z : Ω =>
      (Fin.addCases (fun _ : Fin n => (0 : ℝ)) (fun j : Fin N => A (z.1 j).2) k : ℝ)) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [Fin.addCases_left] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
    · simpa only [Fin.addCases_right,Function.comp_def] using hA.comp (((measurable_pi_apply j).comp measurable_fst).snd)
  change Measurable (fun z : Ω => (π.sampleTags.asFinitePolicy N).selectedTag
    (z.2.2.2,payloadTagSequence t0 (payloadConfigurationMk N z.1))
    (combinedValues z.2.1 (oldPoints z)) (combinedClocks z.2.2.1 (oldPoints z))
    (fun k => Fin.addCases (fun _ : Fin n => 0) (fun j : Fin N => A (z.1 j).2) k))
  exact (π.sampleTags.asFinitePolicy N).measurable_selectedTag
    (π.sampleTags.asFinitePolicy_isMeasurable (π.sampleTags_isMeasurable hπ) N) hr hX hU hTag

omit [MeasurableSpace Seed] in
lemma TaggedHybridRule.payloadSelectedAmplitude_abs_le (π : TaggedHybridRule n Seed T)
    (t0 : T) (A : ℝ × T → ℝ) {D : ℝ} (hD : 0≤D) (hBound : ∀ z, |A z|≤D)
    (v : PayloadConfiguration T × Model.World n Seed) : |π.payloadSelectedAmplitude t0 A v|≤D := by
  apply Model.Policy.selectedTag_abs_le _ _ _ _ _ hD
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [Fin.addCases_left,abs_zero] using hD
  · simpa only [Fin.addCases_right] using hBound (v.1.2 j).2

lemma TaggedHybridRule.integrable_payloadSelectedAmplitude (π : TaggedHybridRule n Seed T)
    (hπ : π.IsMeasurable) (B : FiniteIntensityHybridInstance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (κ : Measure T) [IsProbabilityMeasure κ]
    (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A) {D : ℝ} (hD : 0≤D) (hBound : ∀ z, |A z|≤D) :
    Integrable (π.payloadSelectedAmplitude t0 A) (taggedHybridWorldLaw B ν κ) := by
  apply Integrable.of_bound (π.measurable_payloadSelectedAmplitude hπ t0 A hA).aestronglyMeasurable D
  exact Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact π.payloadSelectedAmplitude_abs_le t0 A hD hBound v)

lemma TaggedHybridRule.integrable_payloadReward (π : TaggedHybridRule n Seed T) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) :
    Integrable (π.payloadReward t0) (taggedHybridWorldLaw B ν κ) := by
  have hMP := sampledTaggedHybridWorld_measurePreserving B ν κ
  have hSource : Integrable (π.sampleTags.realizedReward 0)
      (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ)))) :=
    π.sampleTags.integrable_realizedReward (π.sampleTags_isMeasurable hπ) B.individuals B.intensity _
      (a := 0) (H := (B.cap : ℝ)) le_rfl B.cap.property B.cap.property B.individual_bounded B.intensity_supported
  have hCfg : MeasurePreserving (Prod.fst : HybridWorld n (Seed × (ℕ → T)) → Configuration)
      (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ)))) (configurationLaw B.intensity) := measurePreserving_fst
  have hAE : ∀ᵐ v ∂B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ))),
      π.sampleTags.realizedReward 0 v=π.payloadReward t0 (sampledTaggedHybridWorld v) := by
    filter_upwards [hCfg.quasiMeasurePreserving.ae (configuration_times_distinct B.intensity)] with v hv
    exact (π.payload_outcomes_assigned t0 v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 hv).1.symm
  have hComp : Integrable (π.payloadReward t0 ∘ sampledTaggedHybridWorld)
      (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ)))) := hSource.congr hAE
  exact (hMP.integrable_comp (π.measurable_payloadReward hπ t0).aestronglyMeasurable).mp hComp

end ProphetSecretary.Limiting
