import ProphetSecretary.Limiting.HybridSelectedAmplitudeIntegral

/-!
# Deterministic mark amplitudes recover the anonymous value coefficient

Integrating an independent tag sequence leaves a value-only amplitude
unchanged. This identifies the coefficient with the literal finite-policy
anonymous selected-mark expectation.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {T : Type*} [MeasurableSpace T]

lemma canonicalChronologicalAmplitudeMean_valueOnly (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) [IsProbabilityMeasure κ] (φ : ℝ → ℝ) (hφ : Measurable φ)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    canonicalChronologicalAmplitudeMean B κ (fun z : ℝ × T => φ z.1) w c=
      ∫ v : HybridWorld n Unit,
        ((B.valueRule w c).asFinitePolicy v.1.1).selectedTag ()
          (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
          (Fin.addCases (fun _ : Fin n => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2)))
          ∂B.law (Measure.dirac ()) := by
  let K := Measure.infinitePi (fun _ : ℕ => κ)
  let tag : HybridTags n Unit := fun v =>
    Fin.addCases (fun _ : Fin n => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2))
  have hTag : tag.IsMeasurable := by
    intro N k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [tag,configurationMk,Fin.addCases_left] using
        (measurable_const : Measurable (fun _ : (Fin N → Point) × Model.World n Unit => (0 : ℝ)))
    · simpa only [tag,configurationMk,Fin.addCases_right,Function.comp_def] using
        hφ.comp (((measurable_pi_apply j).comp
          (measurable_fst : Measurable (Prod.fst : ((Fin N → Point) × Model.World n Unit) → _))).snd)
  have hMP := (MeasurePreserving.id (configurationLaw B.intensity)).prod
    ((MeasurePreserving.id B.individuals.valuesLaw).prod
      ((MeasurePreserving.id (Model.Instance.clocksLaw n)).prod
        (measurePreserving_fst : MeasurePreserving (Prod.fst : Unit × (ℕ → T) → Unit)
          ((Measure.dirac ()).prod K) (Measure.dirac ()))))
  have h := hMP.hasLaw.integral_comp
    (measurable_canonicalSelectedAmplitude B hw hc tag hTag).aestronglyMeasurable
  exact h

end ProphetSecretary.Limiting
