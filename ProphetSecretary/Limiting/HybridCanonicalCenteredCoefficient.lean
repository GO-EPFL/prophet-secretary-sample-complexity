import ProphetSecretary.Limiting.TaggedHybridCoefficientStability

/-!
# Centered independent Poisson tags have zero canonical coefficient

The base canonical rule ignores tags. Conditioning on the complete old
instance fixes its selected occurrence; the tag at its chronological rank
still has its original independent law. No future tag is supplied online.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {T : Type} [MeasurableSpace T]

private lemma splitHybridTagSeed_measurePreserving (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) [IsProbabilityMeasure κ] :
    MeasurePreserving (fun v : HybridWorld n (Unit × (ℕ → T)) =>
      ((v.1,(v.2.1,(v.2.2.1,v.2.2.2.1))),v.2.2.2.2))
      (B.law ((Measure.dirac ()).prod (Measure.infinitePi (fun _ : ℕ => κ))))
      ((B.law (Measure.dirac ())).prod (Measure.infinitePi (fun _ : ℕ => κ))) := by
  let K := Measure.infinitePi (fun _ : ℕ => κ)
  let P := B.individuals
  have hOne := (MeasurePreserving.id P.valuesLaw).prod
    ((measurePreserving_prodAssoc (Model.Instance.clocksLaw n) (Measure.dirac ()) K).symm MeasurableEquiv.prodAssoc)
  have hTwo := (measurePreserving_prodAssoc P.valuesLaw ((Model.Instance.clocksLaw n).prod (Measure.dirac ())) K).symm MeasurableEquiv.prodAssoc
  have hOuter := (MeasurePreserving.id (configurationLaw B.intensity)).prod (hTwo.comp hOne)
  have hAssoc := (measurePreserving_prodAssoc (configurationLaw B.intensity) (P.worldLaw (Measure.dirac ())) K).symm MeasurableEquiv.prodAssoc
  exact hAssoc.comp hOuter

lemma canonicalChronologicalAmplitudeMean_centered (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {w c D : ℝ} (hw : 0≤w) (hc : 0≤c) (hD : 0≤D) (hBound : ∀ z, |A z|≤D)
    (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) :
    canonicalChronologicalAmplitudeMean B κ A w c=0 := by
  let K := Measure.infinitePi (fun _ : ℕ => κ)
  let F := fun z : HybridWorld n Unit × (ℕ → T) =>
    ((B.valueRule w c).asFinitePolicy z.1.1.1).selectedTag ()
      (combinedValues z.1.2.1 z.1.1.2) (combinedClocks z.1.2.2.1 z.1.1.2)
      (chronologicalAmplitudeTag A (z.1.1,(z.1.2.1,(z.1.2.2.1,((),z.2)))))
  have hEmbed : Measurable (fun z : HybridWorld n Unit × (ℕ → T) =>
      (z.1.1,(z.1.2.1,(z.1.2.2.1,((),z.2))))) := by fun_prop
  have hMeas : Measurable F :=
    (measurable_canonicalSelectedAmplitude B hw hc (chronologicalAmplitudeTag A)
      (chronologicalAmplitudeTag_isMeasurable A hA)).comp hEmbed
  have hMP := splitHybridTagSeed_measurePreserving B κ
  have hSource := integrable_canonicalSelectedAmplitude B ((Measure.dirac ()).prod K) hw hc
    (chronologicalAmplitudeTag A) (chronologicalAmplitudeTag_isMeasurable A hA) hD
    (chronologicalAmplitudeTag_abs_le A hD hBound)
  have hTarget : Integrable F ((B.law (Measure.dirac ())).prod K) := by
    apply (hMP.integrable_comp hMeas.aestronglyMeasurable).mp
    convert hSource using 1
    funext v
    simp only [Function.comp_def,F,canonicalSelectedAmplitude]
  have hInside (v : HybridWorld n Unit) : (∫ ts, F (v,ts) ∂K)=0 := by
    let basePolicy := (B.valueRule w c).asFinitePolicy v.1.1
    let x := combinedValues v.2.1 v.1.2
    let u := combinedClocks v.2.2.1 v.1.2
    by_cases hs : ∃ k, basePolicy.ActualSelects () Finset.univ x u k
    · obtain ⟨k,hk⟩ := hs
      have hF (ts : ℕ → T) : F (v,ts)=chronologicalAmplitudeTag A
          (v.1,(v.2.1,(v.2.2.1,((),ts)))) k :=
        basePolicy.selectedTag_eq_of_actualSelects () x u _ hk
      simp_rw [hF]
      revert hk
      refine Fin.addCases (fun i _ => ?_) (fun j _ => ?_) k
      · simp only [chronologicalAmplitudeTag,Fin.addCases_left,integral_zero]
      · simp only [chronologicalAmplitudeTag,Fin.addCases_right]
        have hEval := measurePreserving_eval_infinitePi (fun _ : ℕ => κ)
          (Model.Instance.arrivalRank (fun l : Fin v.1.1 => (v.1.2 l).1) j).val
        have hOne : Measurable (fun t : T => A ((v.1.2 j).2,t)) :=
          hA.comp (measurable_const.prodMk measurable_id)
        have hMean := hEval.hasLaw.integral_comp hOne.aestronglyMeasurable
        exact hMean.trans (hCentered (v.1.2 j).2)
    · have hF (ts : ℕ → T) : F (v,ts)=0 :=
        basePolicy.selectedTag_eq_zero_of_no_selection () x u _ (by simpa only [not_exists] using hs)
      simp_rw [hF]
      exact integral_zero _ _
  have hMean := hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable
  change canonicalChronologicalAmplitudeMean B κ A w c=∫ z, F z ∂(B.law (Measure.dirac ())).prod K at hMean
  rw [hMean,integral_prod _ hTarget]
  simp_rw [hInside]
  exact integral_zero _ _

end ProphetSecretary.Limiting
