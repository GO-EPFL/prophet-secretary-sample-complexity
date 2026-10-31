import ProphetSecretary.Model.Truncation
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Retaining offers above a tagged outer cutoff

Each offer receives a fresh independent uniform tag. Lexicographic comparison
uses its numerical value first and the tag second. The fixed-cutoff retained
law is an actual independent product law; zeros remain zero irrespective of tags.
Paper correspondence: the conditional Y_i in `upouter:construction` and
`upouter:cutoff`.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model

/-- Strict lexicographic comparison of value/tag pairs. -/
def taggedAbove (t z : ℝ × ℝ) : Prop := t.1<z.1 ∨ (t.1=z.1 ∧ t.2<z.2)

noncomputable def retainAboveTag (t z : ℝ × ℝ) : ℝ := if taggedAbove t z then z.1 else 0

lemma measurableSet_taggedAbove : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) | taggedAbove p.1 p.2} :=
  (measurableSet_lt (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)).union
    ((measurableSet_eq_fun (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)).inter
      (measurableSet_lt (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)))

lemma measurable_retainAboveTag : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => retainAboveTag p.1 p.2) :=
  (measurable_fst.comp measurable_snd).ite measurableSet_taggedAbove measurable_const

lemma measurable_retainAboveTag_fixed (t : ℝ × ℝ) : Measurable (retainAboveTag t) :=
  measurable_retainAboveTag.comp (measurable_const.prodMk measurable_id)

lemma retainAboveTag_nonneg (t z : ℝ × ℝ) (hz : 0≤z.1) : 0≤retainAboveTag t z := by
  unfold retainAboveTag
  split_ifs <;> linarith only [hz]

lemma retainAboveTag_le_value (t z : ℝ × ℝ) (hz : 0≤z.1) : retainAboveTag t z≤z.1 := by
  unfold retainAboveTag
  split_ifs <;> linarith only [hz]

lemma retainAboveTag_zero (t : ℝ × ℝ) (a : ℝ) : retainAboveTag t (0,a)=0 := by
  unfold retainAboveTag
  split_ifs <;> rfl

namespace Instance
variable {n : ℕ}

noncomputable def taggedValuesLaw (P : Instance n) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun i => (P.law i).prod uniformClock)

instance taggedValuesLaw_probability (P : Instance n) : IsProbabilityMeasure P.taggedValuesLaw := by
  unfold taggedValuesLaw
  infer_instance

noncomputable def retainedAtTag (P : Instance n) (t : ℝ × ℝ) : Instance n where
  law i := ((P.law i).prod uniformClock).map (retainAboveTag t)
  probability i := Measure.isProbabilityMeasure_map (measurable_retainAboveTag_fixed t).aemeasurable
  nonnegative i := by
    apply (ae_map_iff (measurable_retainAboveTag_fixed t).aemeasurable measurableSet_Ici).mpr
    exact ((measurePreserving_fst (μ:=P.law i) (ν:=uniformClock)).quasiMeasurePreserving.ae (P.nonnegative i)).mono
      (fun z hz => retainAboveTag_nonneg t z hz)

lemma taggedValues_projection_measurePreserving (P : Instance n) :
    MeasurePreserving (fun z : Fin n → ℝ × ℝ => fun i => (z i).1) P.taggedValuesLaw P.valuesLaw := by
  have h := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) P.law (fun _ => uniformClock)
  exact measurePreserving_fst.comp h

lemma taggedRetainedValues_measurePreserving (P : Instance n) (t : ℝ × ℝ) :
    MeasurePreserving (fun z : Fin n → ℝ × ℝ => fun i => retainAboveTag t (z i))
      P.taggedValuesLaw (P.retainedAtTag t).valuesLaw := by
  refine ⟨measurable_pi_lambda _ (fun i => (measurable_retainAboveTag_fixed t).comp (measurable_pi_apply i)),?_⟩
  exact Measure.pi_map_pi (fun _ => (measurable_retainAboveTag_fixed t).aemeasurable)

lemma maximum_retainedAtTag_le (t : ℝ × ℝ) (z : Fin n → ℝ × ℝ) :
    maximum (fun i => retainAboveTag t (z i))≤maximum (fun i => (z i).1) := by
  apply maximum_le _ (maximum_nonnegative _)
  intro i
  unfold retainAboveTag
  split_ifs
  · exact le_maximum (fun j : Fin n => (z j).1) i
  · exact maximum_nonnegative _

lemma retainedAtTag_integrable_maximum (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (t : ℝ × ℝ) :
    Integrable maximum (P.retainedAtTag t).valuesLaw := by
  apply ((P.taggedRetainedValues_measurePreserving t).integrable_comp measurable_maximum.aestronglyMeasurable).mp
  have hOriginal := P.taggedValues_projection_measurePreserving.integrable_comp_of_integrable hP
  apply hOriginal.mono' (measurable_maximum.comp (P.taggedRetainedValues_measurePreserving t).measurable).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    change ‖maximum (fun i => retainAboveTag t (z i))‖≤maximum (fun i => (z i).1)
    rw [Real.norm_eq_abs,abs_of_nonneg (maximum_nonnegative _)]
    exact maximum_retainedAtTag_le t z

lemma retainedAtTag_expectedMaximum_le (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (t : ℝ × ℝ) : (P.retainedAtTag t).expectedMaximum≤P.expectedMaximum := by
  have hRet := P.taggedRetainedValues_measurePreserving t
  have hOrig := P.taggedValues_projection_measurePreserving
  have hRetMap := integral_map (μ:=P.taggedValuesLaw) hRet.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
  have hOrigMap := integral_map (μ:=P.taggedValuesLaw) hOrig.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
  rw [hRet.map_eq] at hRetMap
  rw [hOrig.map_eq] at hOrigMap
  change (∫ x, maximum x ∂(P.retainedAtTag t).valuesLaw)≤∫ x, maximum x ∂P.valuesLaw
  rw [hRetMap,hOrigMap]
  exact integral_mono (hRet.integrable_comp_of_integrable (P.retainedAtTag_integrable_maximum hP t))
    (hOrig.integrable_comp_of_integrable hP) (maximum_retainedAtTag_le t)

end Instance
end ProphetSecretary.Model
