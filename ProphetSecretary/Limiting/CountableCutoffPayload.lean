import ProphetSecretary.Limiting.CutoffPayloadLaw
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs

/-!
# A limiting instance after an upper-mark randomized replacement

The actual independent-tag intensity is pushed through the cutoff display.
Images at or below the terminal reserve are omitted, as permitted in the
limiting model. Positive tails remain finite because affected original marks
come from a fixed finite upper band. Individual identities are unchanged.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type*} [MeasurableSpace T]

noncomputable def mapPoissonAbove (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) : CountableInstance where
  cap := H
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap.trans hH
  individuals := B.individuals
  individual_supported i := (B.individual_supported i).mono (fun _ hx => ⟨hx.1,hx.2.trans hH⟩)
  intensity := ((B.intensity.prod κ).map (cutoffPayloadDisplay b Φ)).restrict (Ioi (B.terminal : ℝ))
  intensity_supported := by
    have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) (B.intensity.prod κ) B.intensity := measurePreserving_fst
    have hCap : ∀ᵐ y ∂(B.intensity.prod κ).map (cutoffPayloadDisplay b Φ), y≤(H : ℝ) := by
      apply (ae_map_iff (measurable_cutoffPayloadDisplay b hΦ).aemeasurable measurableSet_Iic).mpr
      filter_upwards [hMP.quasiMeasurePreserving.ae B.intensity_supported,hImage] with z hz hφ
      unfold cutoffPayloadDisplay
      split_ifs with h
      · exact (hφ h).2
      · exact hz.2.trans hH
    filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae hCap] with y hy hY
    exact ⟨hy,hY⟩
  individual_tail_finite := B.individual_tail_finite
  intensity_tail_finite d hd := by
    have hMin : (B.terminal : ℝ)<min b d := lt_min hb hd
    have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) (B.intensity.prod κ) B.intensity := measurePreserving_fst
    rw [Measure.restrict_apply measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hd.le),
      Measure.map_apply (measurable_cutoffPayloadDisplay b hΦ) measurableSet_Ioi]
    calc
      _ ≤ (B.intensity.prod κ) (Prod.fst ⁻¹' Ioi (min b d)) :=
        measure_mono (cutoffPayloadDisplay_tail_preimage b d Φ)
      _ = B.intensity (Ioi (min b d)) := hMP.measure_preimage measurableSet_Ioi.nullMeasurableSet
      _ < ⊤ := B.intensity_tail_finite _ hMin

lemma mapPoissonAbove_intensity (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).intensity=
      B.intensity.restrict (Iic b)+(displayedPayloadIntensity (B.intensityAbove b hb) κ Φ hΦ : Measure ℝ).restrict (Ioi (B.terminal : ℝ)) := by
  change ((B.intensity.prod κ).map (cutoffPayloadDisplay b Φ)).restrict (Ioi (B.terminal : ℝ))=_
  rw [map_cutoffPayloadDisplay B.intensity κ b Φ hΦ,Measure.restrict_add]
  have hLow : (B.intensity.restrict (Iic b)).restrict (Ioi (B.terminal : ℝ))=B.intensity.restrict (Iic b) := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_restrict_of_ae B.intensity_supported).mono (fun _ hx => hx.1)
  rw [hLow,displayedPayloadIntensity_toMeasure]
  rfl

end ProphetSecretary.Limiting.CountableInstance
