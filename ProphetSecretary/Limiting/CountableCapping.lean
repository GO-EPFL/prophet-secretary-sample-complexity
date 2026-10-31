import ProphetSecretary.Limiting.CountableInstance
import ProphetSecretary.Model.Truncation

/-!
# Capping a zero-reserve countable instance

Capping is applied to every individual law and to the anonymous intensity.
A positive cap preserves positive anonymous observations; individual zeros and
identities are retained. The original ambient bound and band geometry remain
fixed, while every capped mark is additionally bounded by K. Tail finiteness follows by a literal tail
comparison of the pushforward measures.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma capValue_tail_preimage_subset (K : ℝ≥0) (b : ℝ) :
    Model.capValue K ⁻¹' Ioi b⊆Ioi b := by
  intro x hx
  change b<min x (K:ℝ) at hx
  exact hx.trans_le (min_le_left _ _)

noncomputable def capAt (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) : CountableInstance where
  cap := B.cap
  terminal := 0
  terminal_le_cap := B.cap.property
  individuals i := ⟨(B.individuals i : Measure ℝ).map (Model.capValue K),
    Measure.isProbabilityMeasure_map (Model.measurable_capValue K).aemeasurable⟩
  individual_supported i := by
    apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Icc).mpr
    filter_upwards [B.individual_supported i] with x hx
    exact ⟨le_min hx.1 K.property,(min_le_left _ _).trans hx.2⟩
  intensity := B.intensity.map (Model.capValue K)
  intensity_supported := by
    apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Ioc).mpr
    filter_upwards [B.intensity_supported] with x hx
    have hx0 : 0<x := by simpa only [hZero,NNReal.coe_zero] using hx.1
    exact ⟨lt_min hx0 (show (0:ℝ)<K from hK),(min_le_left _ _).trans hx.2⟩
  individual_tail_finite b hb := by
    have hOld : (B.terminal:ℝ)<b := by simpa only [hZero,NNReal.coe_zero] using hb
    apply lt_of_le_of_lt ?_ (B.individual_tail_finite b hOld)
    apply ENNReal.tsum_le_tsum
    intro i
    change ((B.individuals i : Measure ℝ).map (Model.capValue K)) (Ioi b)≤(B.individuals i : Measure ℝ) (Ioi b)
    rw [Measure.map_apply (Model.measurable_capValue K) measurableSet_Ioi]
    exact measure_mono (capValue_tail_preimage_subset K b)
  intensity_tail_finite b hb := by
    have hOld : (B.terminal:ℝ)<b := by simpa only [hZero,NNReal.coe_zero] using hb
    rw [Measure.map_apply (Model.measurable_capValue K) measurableSet_Ioi]
    exact lt_of_le_of_lt (measure_mono (capValue_tail_preimage_subset K b)) (B.intensity_tail_finite b hOld)

@[simp] lemma capAt_terminal (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) :
    (B.capAt hZero K hK).terminal=0 := rfl

@[simp] lemma capAt_cap (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) :
    (B.capAt hZero K hK).cap=B.cap := rfl

lemma capAt_individual_tail (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (i : ℕ) {b : ℝ} (hb : b<(K:ℝ)) :
    ((B.capAt hZero K hK).individuals i : Measure ℝ) (Ioi b)=(B.individuals i : Measure ℝ) (Ioi b) := by
  rw [show ((B.capAt hZero K hK).individuals i : Measure ℝ)=(B.individuals i : Measure ℝ).map (Model.capValue K) from rfl,
    Measure.map_apply (Model.measurable_capValue K) measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_Ioi,Model.capValue,lt_min_iff,hb,and_true]

lemma capAt_intensity_tail (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    {b : ℝ} (hb : b<(K:ℝ)) :
    (B.capAt hZero K hK).intensity (Ioi b)=B.intensity (Ioi b) := by
  rw [show (B.capAt hZero K hK).intensity=B.intensity.map (Model.capValue K) from rfl,
    Measure.map_apply (Model.measurable_capValue K) measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_Ioi,Model.capValue,lt_min_iff,hb,and_true]

end ProphetSecretary.Limiting.CountableInstance
