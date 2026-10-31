import ProphetSecretary.Limiting.CountableBandScore

/-!
# Exact real tail intensities of a scaled band

The total intensity may be infinite. Every strict upper tail is finite, so
the complement/band decomposition and its real arithmetic are exact there,
including a zero scaling factor.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma scaleBand_intensity_measure (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S) (r : ℝ≥0) :
    (B.scaleBand S r).intensity=B.intensity.restrict Sᶜ+(r : ℝ≥0∞) • B.intensity.restrict S := by
  change B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x))=_
  have hFunction : (fun x => ENNReal.ofReal (bandScaleFactor S r x))=
      S.indicator (fun _ => (r : ℝ≥0∞))+Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x∈S <;> simp [bandScaleFactor,hx]
  rw [hFunction,withDensity_add_left (measurable_const.indicator hS),
    withDensity_indicator hS,withDensity_indicator hS.compl,withDensity_const,withDensity_const,one_smul]
  exact add_comm _ _

lemma scaleBand_intensity_tail_real (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (r : ℝ≥0) {t : ℝ} (ht : (B.terminal : ℝ)<t) :
    (B.scaleBand S r).intensity.real (Ioi t)=B.intensity.real (Ioi t∩Sᶜ)+(r : ℝ)*B.intensity.real (Ioi t∩S) := by
  have hFinite : B.intensity (Ioi t)≠⊤ := (B.intensity_tail_finite t ht).ne
  have hComp : B.intensity (Ioi t∩Sᶜ)≠⊤ := (measure_mono inter_subset_left).trans_lt (B.intensity_tail_finite t ht) |>.ne
  have hBand : B.intensity (Ioi t∩S)≠⊤ := (measure_mono inter_subset_left).trans_lt (B.intensity_tail_finite t ht) |>.ne
  change ((B.scaleBand S r).intensity (Ioi t)).toReal=_
  rw [B.scaleBand_intensity_measure hS r,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_Ioi,Measure.restrict_apply measurableSet_Ioi,
    ENNReal.toReal_add hComp (ENNReal.mul_ne_top (by finiteness) hBand),ENNReal.toReal_mul]
  rfl

lemma band_tail_real_le (B : CountableInstance) {S : Set ℝ} {b : ℝ}
    (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) (t : ℝ) :
    B.intensity.real (Ioi t∩S)≤B.intensity.real S :=
  measureReal_mono inter_subset_right (B.intensity_band_finite hb hSub).ne

end ProphetSecretary.Limiting.CountableInstance
