import ProphetSecretary.Probability.ProductConditioning

/-!
# Conditional expectation from stationary resampling

If resampling preserves a law and the observed projection, integrating the fresh
coordinate gives the conditional expectation. The applications to uniform clocks
prove the resampling law and observation invariance from their product model.
-/

open MeasureTheory Set

namespace ProphetSecretary.Probability

variable {Ω Ξ Γ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ] [mΓ : MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma condExp_stationaryResampling {C : Ω → Γ} {R : Γ × Ξ → Ω}
    (hC : Measurable C) (hR : Measurable R)
    (hPres : MeasurePreserving (fun q : Ω × Ξ => R (C q.1, q.2)) (μ.prod ν) μ)
    (hObs : ∀ᵐ q : Ω × Ξ ∂μ.prod ν, C (R (C q.1, q.2)) = C q.1)
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    μ[f | mΓ.comap C] =ᵐ[μ] (fun ω => ∫ v, f (R (C ω, v)) ∂ν) := by
  classical
  let H : Γ → ℝ := fun a => ∫ v, f (R (a, v)) ∂ν
  let G : Ω → ℝ := fun ω => H (C ω)
  have hFR : Integrable (fun q : Ω × Ξ => f (R (C q.1, q.2))) (μ.prod ν) :=
    hPres.integrable_comp_of_integrable hf
  have hH : StronglyMeasurable H := (hfm.comp hR).stronglyMeasurable.integral_prod_right'
  have hGm : StronglyMeasurable[mΓ.comap C] G := by
    letI : MeasurableSpace Ω := mΓ.comap C
    have hmC : Measurable C := Measurable.of_comap_le le_rfl
    exact hH.comp_measurable hmC
  have hGI : Integrable G μ := hFR.integral_prod_left
  have hCE : G =ᵐ[μ] μ[f | mΓ.comap C] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hC.comap_le hf
      (fun _ _ _ => hGI.integrableOn) ?_ hGm.aestronglyMeasurable
    intro A hA _hfinite
    have hAm : MeasurableSet A := hC.comap_le A hA
    obtain ⟨s, hs, he⟩ := MeasurableSpace.measurableSet_comap.mp hA
    have hIndicator : (fun q : Ω × Ξ => A.indicator f (R (C q.1, q.2))) =ᵐ[μ.prod ν]
        (fun q => (A ×ˢ (Set.univ : Set Ξ)).indicator (fun q => f (R (C q.1, q.2))) q) := by
      filter_upwards [hObs] with q hq
      have hm : R (C q.1, q.2) ∈ A ↔ q.1 ∈ A := by
        rw [← he]
        simp only [mem_preimage, hq]
      by_cases ha : q.1 ∈ A
      · rw [Set.indicator_of_mem (hm.mpr ha), Set.indicator_of_mem (show q ∈ A ×ˢ (Set.univ : Set Ξ) from ⟨ha, Set.mem_univ _⟩)]
      · rw [Set.indicator_of_notMem (fun h => ha (hm.mp h)), Set.indicator_of_notMem (fun h => ha h.1)]
    have hmap := integral_map (μ := μ.prod ν) hPres.measurable.aemeasurable (hfm.indicator hAm).aestronglyMeasurable
    rw [hPres.map_eq, integral_indicator hAm] at hmap
    have hprod := integral_congr_ae hIndicator
    rw [integral_indicator (hAm.prod MeasurableSet.univ)] at hprod
    have hFub := setIntegral_prod (fun q : Ω × Ξ => f (R (C q.1, q.2)))
      (s := A) (t := (Set.univ : Set Ξ)) hFR.integrableOn
    simp only [Measure.restrict_univ] at hFub
    exact hFub.symm.trans (hprod.symm.trans hmap.symm)
  exact hCE.symm

end ProphetSecretary.Probability
