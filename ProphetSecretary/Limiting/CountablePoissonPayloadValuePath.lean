import ProphetSecretary.Limiting.HybridPoissonValuePath
import ProphetSecretary.Limiting.BandGeneratingFunctional

/-!
# Bounded tagged displacements of a locally finite Poisson intensity

Independent occurrence tags are integrated into the pushforward intensity.
The display is the identity below a fixed positive level. Thus its positive
level tails remain finite even when the full original intensity is infinite.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T]

omit [MeasurableSpace T] in
lemma payloadValueDisplay_tail_preimage_subset {A : ℝ × T → ℝ} {D b d θ : ℝ}
    (hb : 0<b) (hVanish : ∀ z, z.1<b → A z=0) :
    payloadValueDisplay A D b θ ⁻¹' Ioi d ⊆ Prod.fst ⁻¹' Ioi (min d (b/2)) := by
  intro z hz
  by_contra hn
  have hx : z.1≤min d (b/2) := not_lt.mp hn
  have hxb : z.1<b := lt_of_le_of_lt (hx.trans (min_le_right _ _)) (by linarith)
  have hg : payloadValueDisplay A D b θ z=z.1 := by
    unfold payloadValueDisplay
    split_ifs <;> simp only [hVanish z hxb,mul_zero,add_zero]
  change d<payloadValueDisplay A D b θ z at hz
  rw [hg] at hz
  exact (not_lt_of_ge (hx.trans (min_le_left _ _))) hz

noncomputable def poissonPayloadValuePath (B : CountableInstance) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    (D b : ℝ) (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ) : CountableInstance where
  cap := B.cap+1
  terminal := 0
  terminal_le_cap := (B.cap+1).property
  individuals := B.individuals
  individual_supported i := (B.individual_supported i).mono (fun _ hx =>
    ⟨hx.1,hx.2.trans (by simp only [NNReal.coe_add,NNReal.coe_one]; linarith)⟩)
  intensity := (B.intensity.prod κ).map (payloadValueDisplay A D b θ)
  intensity_supported := by
    apply (ae_map_iff (measurable_payloadValueDisplay hA D b θ).aemeasurable measurableSet_Ioc).mpr
    have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) (B.intensity.prod κ) B.intensity := measurePreserving_fst
    filter_upwards [hMP.quasiMeasurePreserving.ae B.intensity_supported] with z hz
    have hz0 : z.1∈Ioc (0 : ℝ) B.cap := by simpa only [hZero,NNReal.coe_zero] using hz
    exact payloadValueDisplay_positive_bounds hD hb hBound hVanish θ z hz0
  individual_tail_finite d hd := B.individual_tail_finite d (by simpa only [hZero,NNReal.coe_zero] using hd)
  intensity_tail_finite d hd := by
    rw [Measure.map_apply (measurable_payloadValueDisplay hA D b θ) measurableSet_Ioi]
    have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) (B.intensity.prod κ) B.intensity := measurePreserving_fst
    calc
      _ ≤ (B.intensity.prod κ) (Prod.fst ⁻¹' Ioi (min d (b/2))) :=
        measure_mono (payloadValueDisplay_tail_preimage_subset hb hVanish)
      _ = B.intensity (Ioi (min d (b/2))) := hMP.measure_preimage measurableSet_Ioi.nullMeasurableSet
      _ < ⊤ := B.intensity_tail_finite _ (by simpa only [hZero,NNReal.coe_zero] using lt_min hd (by positivity : 0<b/2))

lemma poissonPayloadValuePath_zero (B : CountableInstance) (hZero : B.terminal=0)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) :
    B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish 0=B.withCap (B.cap+1) (by simp) := by
  apply CountableInstance.ext_data
  · rfl
  · exact hZero.symm
  · rfl
  · change (B.intensity.prod κ).map (payloadValueDisplay A D b 0)=B.intensity
    rw [payloadValueDisplay_zero]
    exact (measurePreserving_fst : MeasurePreserving (Prod.fst : ℝ × T → ℝ) (B.intensity.prod κ) B.intensity).map_eq

end ProphetSecretary.Limiting.CountableInstance
