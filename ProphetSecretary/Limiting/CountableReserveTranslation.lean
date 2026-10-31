import ProphetSecretary.Limiting.LabeledValueConvergence
import ProphetSecretary.Model.ExcessPositiveTail
import ProphetSecretary.Limiting.WeakExcessLaws

/-!
# Translating a positive terminal reserve and all offer values

The actual laws are pushed through the continuous excess map. Since every
retained Poisson mark exceeds the old reserve, it stays strictly above the
translated reserve. Positive-level tail identities give local finiteness.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting
open Model

lemma excessValueMap_preimage_Ioi {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    excessValueMap a ⁻¹' Ioi b=Ioi (a+b) := by
  ext x
  exact excessValueMap_gt_iff ha hb

lemma excessValueMap_preimage_singleton {a b : ℝ} (ha : 0≤a) (hb : 0<b) :
    excessValueMap a ⁻¹' {b}={a+b} := by
  ext x
  simp only [mem_preimage,mem_singleton_iff]
  constructor
  · intro he
    have hx : 0<excessValueMap a x := hb.trans_eq he.symm
    exact (positive_excess_reconstructs_value ha hx).trans (congrArg (fun y => a+y) he)
  · rintro rfl
    rw [excessValueMap_eq_positivePart (by linarith : 0≤a+b),add_sub_cancel_left,
      max_eq_left hb.le]

namespace CountableInstance

noncomputable def reserveTranslation (B : CountableInstance) (a : ℝ≥0) (ha : a<B.terminal) : CountableInstance where
  cap := B.cap
  terminal := B.terminal-a
  terminal_le_cap := (tsub_le_self : B.terminal-a≤B.terminal).trans B.terminal_le_cap
  individuals i := (B.individuals i).map (measurable_excessValueMap a).aemeasurable
  individual_supported i := by
    apply (ae_map_iff (measurable_excessValueMap a).aemeasurable measurableSet_Icc).mpr
    exact (B.individual_supported i).mono (fun x hx =>
      ⟨excessValueMap_nonnegative hx.1,(excessValueMap_le_self a.property x).trans hx.2⟩)
  intensity := B.intensity.map (excessValueMap a)
  intensity_supported := by
    apply (ae_map_iff (measurable_excessValueMap a).aemeasurable measurableSet_Ioc).mpr
    filter_upwards [B.intensity_supported] with x hx
    have hax : (a : ℝ)<x := (show (a : ℝ)<B.terminal by exact_mod_cast ha).trans hx.1
    have hx0 : 0≤x := a.property.trans hax.le
    rw [excessValueMap_eq_positivePart hx0,max_eq_left (sub_nonneg.mpr hax.le),NNReal.coe_sub ha.le]
    exact ⟨sub_lt_sub_right hx.1 _,(sub_le_self _ a.property).trans hx.2⟩
  individual_tail_finite b hb := by
    have hb0 : 0≤b := (B.terminal-a).property.trans hb.le
    have hOld : (B.terminal : ℝ)<(a : ℝ)+b := by rw [NNReal.coe_sub ha.le] at hb; linarith only [hb]
    change (∑' i, excessLaw (B.individuals i : Measure ℝ) a (Ioi b))<⊤
    calc
      (∑' i, excessLaw (B.individuals i : Measure ℝ) a (Ioi b))=
          ∑' i, (B.individuals i : Measure ℝ) (Ioi ((a : ℝ)+b)) := tsum_congr (fun i =>
        Model.excessLaw_positiveTail (B.individuals i : Measure ℝ) (a := (a : ℝ)) (b := b) a.property hb0)
      _ < ⊤ := B.individual_tail_finite _ hOld
  intensity_tail_finite b hb := by
    have hb0 : 0≤b := (B.terminal-a).property.trans hb.le
    have hOld : (B.terminal : ℝ)<(a : ℝ)+b := by rw [NNReal.coe_sub ha.le] at hb; linarith only [hb]
    change excessLaw B.intensity a (Ioi b)<⊤
    exact lt_of_eq_of_lt
      (Model.excessLaw_positiveTail B.intensity (a := (a : ℝ)) (b := b) a.property hb0)
      (B.intensity_tail_finite _ hOld)

lemma reserveTranslation_intensityAbove (B : CountableInstance) (a : ℝ≥0) (ha : a<B.terminal)
    (b : ℝ) (hb : ((B.reserveTranslation a ha).terminal : ℝ)<b) :
    (B.reserveTranslation a ha).intensityAbove b hb=
      (B.intensityAbove ((a : ℝ)+b) (by
        change ((B.terminal-a : ℝ≥0) : ℝ)<b at hb
        rw [NNReal.coe_sub ha.le] at hb
        linarith only [hb])).map (excessValueMap a) := by
  apply FiniteMeasure.toMeasure_injective
  have hb0 : 0≤b := (B.terminal-a).property.trans hb.le
  change (B.intensity.map (excessValueMap a)).restrict (Ioi b)=
    (B.intensity.restrict (Ioi ((a : ℝ)+b))).map (excessValueMap a)
  rw [Measure.restrict_map (measurable_excessValueMap a) measurableSet_Ioi]
  have hPre : excessValueMap (a : ℝ) ⁻¹' Ioi b=Ioi ((a : ℝ)+b) :=
    excessValueMap_preimage_Ioi (a := (a : ℝ)) (b := b) a.property hb0
  exact congrArg (fun S => (B.intensity.restrict S).map (excessValueMap a)) hPre

end CountableInstance
end ProphetSecretary.Limiting
