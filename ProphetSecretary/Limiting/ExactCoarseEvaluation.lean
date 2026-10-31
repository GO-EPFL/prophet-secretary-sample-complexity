import ProphetSecretary.Limiting.FiniteCutoffScoreOutcomes
import ProphetSecretary.Limiting.ThresholdedWorldPoisson

/-!
# Exact-intensity Poisson comparison for a fixed coarse execution

When the aggregate intensity of the observed high points is eventually exact,
marked Poisson comparison applies to every bounded measurable outcome test.
The callback may be designed for a different law and stays fixed throughout.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

lemma exactIntensity_observable_tendsto {Aux : Type*} [MeasurableSpace Aux]
    (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m)) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (d : ℝ) (μ : FiniteMeasure ℝ)
    (hExact : ∀ᶠ m in atTop, (∑ i, thresholdMarkIntensity ((Q m).law i) d)=μ)
    (hSquares : Tendsto (fun m => ∑ i, (((Q m).law i).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    (G : (Measure Point) × Aux → ℝ) (hG : Measurable G) {D : ℝ} (hD : 0≤D)
    (hBound : ∀ z, |G z|≤D) :
    Tendsto (fun m => ∫ ω : Model.World (sizes m) Aux,
      G (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ν) atTop
      (𝓝 (∫ q : Configuration × Aux, G (countingMeasure q.1,q.2) ∂(configurationLaw μ).prod ν)) := by
  let C := ∫ q : Configuration × Aux, G (countingMeasure q.1,q.2) ∂(configurationLaw μ).prod ν
  have hBound' : ∀ᶠ m in atTop,
      |(∫ ω : Model.World (sizes m) Aux, G (thresholdedOfferCountingMeasure d
        (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ν)-C|≤2*D*∑ i, (((Q m).law i).real (Ioi d))^2 := by
    filter_upwards [hExact] with m hm
    have h := thresholdedWorld_poisson_observable_error (Q m) ν d G hG hD hBound
    rw [hm] at h
    exact h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [show (fun m => ‖(∫ ω : Model.World (sizes m) Aux, G (thresholdedOfferCountingMeasure d
      (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ν)-C‖)=
    (fun m => |(∫ ω : Model.World (sizes m) Aux, G (thresholdedOfferCountingMeasure d
      (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ν)-C|) by rfl]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hBound'
    (by simpa only [mul_zero] using hSquares.const_mul (2*D))

 theorem RandomizedHybridPolicy.finiteCutoffEvaluation_exactIntensity_tendsto {n : ℕ}
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m)) (d : ℝ)
    (hCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(B.cap:ℝ))
    (hExact : ∀ᶠ m in atTop, (∑ i, thresholdMarkIntensity ((Q m).law i) d)=B.intensity)
    (hSquares : Tendsto (fun m => ∑ i, (((Q m).law i).real (Ioi d))^2) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => (π.finiteCutoffEvaluation (sizes m) d).expectedReward (B.individuals.appendIndependent (Q m)))
      atTop (𝓝 (π.expectedReward B)) ∧
    Tendsto (fun m => (π.finiteCutoffEvaluation (sizes m) d).expectedDuration (B.individuals.appendIndependent (Q m)))
      atTop (𝓝 (π.expectedDuration B)) := by
  let GR := hybridOutcomeObservable π (fun z => boundedClamp B.cap z.1.1)
  let GT := hybridOutcomeObservable π (fun z => boundedClamp 1 z.1.2)
  have hGR : Measurable GR := measurable_hybridOutcomeObservable π _ ((boundedClamp B.cap).continuous.measurable.comp (by fun_prop))
  have hGT : Measurable GT := measurable_hybridOutcomeObservable π _ ((boundedClamp 1).continuous.measurable.comp (by fun_prop))
  have hRB (z) : |GR z|≤(B.cap:ℝ) := by
    change |boundedClamp B.cap _|≤_
    rw [abs_of_nonneg (boundedClamp_bounds B.cap _).1]
    exact (boundedClamp_bounds B.cap _).2
  have hTB (z) : |GT z|≤1 := by
    change |boundedClamp 1 _|≤_
    rw [abs_of_nonneg (boundedClamp_bounds 1 _).1]
    exact (boundedClamp_bounds 1 _).2
  have hR := exactIntensity_observable_tendsto sizes Q (B.individuals.worldLaw π.seedLaw) d B.intensity hExact hSquares GR hGR B.cap.property hRB
  have hT := exactIntensity_observable_tendsto sizes Q (B.individuals.worldLaw π.seedLaw) d B.intensity hExact hSquares GT hGT (by norm_num) hTB
  have hFinite (m) := π.finiteCutoffEvaluation_score_coordinate_tests B.individuals (Q m) d B.cap B.individual_bounded (hCap m)
    (fun _ => 1) measurable_const (integrable_const 1)
  have hFiniteR (m) : (π.finiteCutoffEvaluation (sizes m) d).expectedReward (B.individuals.appendIndependent (Q m))=
      ∫ ω : Model.World (sizes m) (Model.World n π.Seed), GR (thresholdedOfferCountingMeasure d
        (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw (B.individuals.worldLaw π.seedLaw) := by
    have h := (hFinite m).1.2
    simp only [one_mul] at h
    convert h using 1 <;> rfl
  have hFiniteT (m) : (π.finiteCutoffEvaluation (sizes m) d).expectedDuration (B.individuals.appendIndependent (Q m))=
      ∫ ω : Model.World (sizes m) (Model.World n π.Seed), GT (thresholdedOfferCountingMeasure d
        (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw (B.individuals.worldLaw π.seedLaw) := by
    have h := (hFinite m).2.2
    simp only [one_mul] at h
    convert h using 1 <;> rfl
  have hObs := hybridOutcomeObservable_eq_ae π B.individuals B.intensity B.cap B.individual_bounded B.intensity_supported
  have hRanges := hybrid_policy_outcome_ranges π B.individuals B.intensity B.cap B.individual_bounded B.intensity_supported
  have hTargetR : (∫ q : Configuration × Model.World n π.Seed, GR (countingMeasure q.1,q.2)
      ∂(configurationLaw B.intensity).prod (B.individuals.worldLaw π.seedLaw))=π.expectedReward B := by
    change (∫ q, GR (countingMeasure q.1,q.2) ∂B.law π.seedLaw)=_
    unfold RandomizedHybridPolicy.expectedReward HybridRule.expectedReward
    rw [hZero]
    apply integral_congr_ae
    filter_upwards [hObs (fun z => boundedClamp B.cap z.1.1),hRanges] with q hq hRange
    exact hq.trans (boundedClamp_eq B.cap hRange.1)
  have hTargetT : (∫ q : Configuration × Model.World n π.Seed, GT (countingMeasure q.1,q.2)
      ∂(configurationLaw B.intensity).prod (B.individuals.worldLaw π.seedLaw))=π.expectedDuration B := by
    change (∫ q, GT (countingMeasure q.1,q.2) ∂B.law π.seedLaw)=_
    unfold RandomizedHybridPolicy.expectedDuration HybridRule.meanDuration
    apply integral_congr_ae
    filter_upwards [hObs (fun z => boundedClamp 1 z.1.2),hRanges] with q hq hRange
    exact hq.trans (boundedClamp_eq 1 hRange.2)
  rw [hTargetR] at hR
  rw [hTargetT] at hT
  exact ⟨hR.congr (fun m => (hFiniteR m).symm),hT.congr (fun m => (hFiniteT m).symm)⟩
end ProphetSecretary.Limiting
