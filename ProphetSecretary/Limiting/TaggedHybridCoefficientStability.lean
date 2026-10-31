import ProphetSecretary.Limiting.HybridSelectedAmplitudeIntegral
import ProphetSecretary.Limiting.TaggedHybridLinearValue

/-!
# Stability of selected Poisson perturbation coefficients

A bounded amplitude supported above a positive level is a common measurable
selected-occurrence tag. The coefficient modulus is uniform in the retained
dimension and total intensity, depending only on the positive-tail profile.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
variable {T : Type} [MeasurableSpace T]

omit [MeasurableSpace T] in
lemma chronologicalAmplitudeTag_abs_le {n : ℕ} {Seed : Type*}
    (A : ℝ × T → ℝ) {D : ℝ} (hD : 0≤D) (hBound : ∀ z, |A z|≤D)
    (v : HybridWorld n (Seed × (ℕ → T))) (k : Fin (n+v.1.1)) :
    |chronologicalAmplitudeTag A v k|≤D := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [chronologicalAmplitudeTag,Fin.addCases_left,abs_zero] using hD
  · simpa only [chronologicalAmplitudeTag,Fin.addCases_right] using
      hBound ((v.1.2 j).2,v.2.2.2.2 (Model.Instance.arrivalRank (fun l : Fin v.1.1 => (v.1.2 l).1) j).val)

omit [MeasurableSpace T] in
lemma chronologicalAmplitudeTag_zero {n : ℕ} {Seed : Type*} (A : ℝ × T → ℝ) {b : ℝ}
    (hVanish : ∀ z, z.1<b → A z=0) (v : HybridWorld n (Seed × (ℕ → T)))
    (k : Fin (n+v.1.1)) (hk : combinedValues v.2.1 v.1.2 k<b) :
    chronologicalAmplitudeTag A v k=0 := by
  revert hk
  refine Fin.addCases (fun i _ => ?_) (fun j hj => ?_) k
  · simp only [chronologicalAmplitudeTag,Fin.addCases_left]
  · simp only [chronologicalAmplitudeTag,Fin.addCases_right]
    exact hVanish _ (by simpa only [combinedValues,Fin.addCases_right] using hj)

lemma RandomizedTaggedHybridPolicy.payloadAmplitudeMean_abs_le {n : ℕ}
    (π : RandomizedTaggedHybridPolicy n T) (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (A : ℝ × T → ℝ)
    {D : ℝ} (hD : 0≤D) (hBound : ∀ z, |A z|≤D) :
    |π.payloadAmplitudeMean B κ t0 A|≤D := by
  have h := norm_integral_le_of_norm_le_const (μ := taggedHybridWorldLaw B π.seedLaw κ)
    (f := π.rule.payloadSelectedAmplitude t0 A) (C := D)
    (Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact π.rule.payloadSelectedAmplitude_abs_le t0 A hD hBound v))
  simpa only [RandomizedTaggedHybridPolicy.payloadAmplitudeMean,Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using h

lemma RandomizedTaggedHybridPolicy.payloadAmplitudeMean_canonical_error {n : ℕ}
    (π : RandomizedTaggedHybridPolicy n T) (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A)
    {w c D : ℝ} (hw : 0≤w) (hc : 0≤c) (hD : 0≤D) (hBound : ∀ z, |A z|≤D) :
    |π.payloadAmplitudeMean B κ t0 A-canonicalChronologicalAmplitudeMean B κ A w c|≤
      (π.sampleTags κ).expectedSelectedTagError B w c (chronologicalAmplitudeTag A) := by
  let tag := chronologicalAmplitudeTag (n := n) (Seed := π.Seed) A
  have hTag := chronologicalAmplitudeTag_isMeasurable (n := n) (Seed := π.Seed) A hA
  have hB : ∀ v k, |tag v k|≤D := chronologicalAmplitudeTag_abs_le A hD hBound
  have hπI := π.rule.sampleTags.integrable_selectedAmplitude
    (π.rule.sampleTags_isMeasurable π.measurable_rule) B
    (π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => κ))) tag hTag hD hB
  have hρI := integrable_canonicalSelectedAmplitude B
    (π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => κ))) hw hc tag hTag hD hB
  have hMean := π.rule.integral_payloadSelectedAmplitude_eq π.measurable_rule B π.seedLaw κ t0 A hA
  have hCanonical := canonicalChronologicalAmplitudeMean_seed B κ A hA π.seedLaw hw hc
  change |(∫ v, π.rule.payloadSelectedAmplitude t0 A v ∂taggedHybridWorldLaw B π.seedLaw κ)-_|≤_
  rw [hMean,← hCanonical]
  change |(∫ v, π.rule.sampleTags.selectedAmplitude tag v ∂B.law
      (π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => κ))))-
    (∫ v, canonicalSelectedAmplitude B w c tag v ∂B.law
      (π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => κ))))|≤_
  rw [← integral_sub hπI hρI]
  exact abs_integral_le_integral_abs

theorem tagged_hybrid_coefficient_stability {α : Type*} (n : α → ℕ)
    (B : ∀ a, FiniteIntensityHybridInstance (n a)) {H w c D b : ℝ}
    (hH : 0≤H) (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ)≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d)
    (hTail : ∀ a d, 0<d → (B a).tailCount d≤L d) :
    ∃ ψ : ℝ → ℝ, (∀ t, 0≤ψ t) ∧ Monotone ψ ∧ ψ 0=0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T)
        (A : ℝ × T → ℝ), Measurable A → (∀ z, |A z|≤D) →
        (∀ z, z.1<b → A z=0) → ∀ a (π : RandomizedTaggedHybridPolicy (n a) T),
        |π.payloadAmplitudeMean (B a) κ t0 A-canonicalChronologicalAmplitudeMean (B a) κ A w c|≤
          ψ ((B a).optimalScalarValue w c-(π.sampleTags κ).scalarObjective (B a) w c) := by
  obtain ⟨ψ,hψ,hMono,hZero,hLim,hBound⟩ :=
    finite_hybrid_selectedOccurrence_stability_fixed_weights n B hH hw hc hD hb ha hCap L hL hTail
  refine ⟨ψ,hψ,hMono,hZero,hLim,?_⟩
  intro κ _ t0 A hA hABound hVanish a π
  exact (π.payloadAmplitudeMean_canonical_error (B a) κ t0 A hA hw.le hc.le hD hABound).trans
    (hBound a (π.sampleTags κ) (chronologicalAmplitudeTag A)
      (chronologicalAmplitudeTag_isMeasurable A hA)
      (Eventually.of_forall (fun v k => chronologicalAmplitudeTag_abs_le A hD hABound v k))
      (Eventually.of_forall (fun v k hk => chronologicalAmplitudeTag_zero A hVanish v k hk)))

end ProphetSecretary.Limiting
