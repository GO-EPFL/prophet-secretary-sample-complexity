import ProphetSecretary.Model.OuterRetentionConditioning

/-!
# Retained maximum laws and measurable population pilot tails

Population probabilities are analytical functions of the fixed cutoff and pilot
value. They are not observations supplied to a learner. Their measurability is
proved by integrating the actual fresh tagged-offer comparison indicators.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def retainedMaximumAtTag (t : ℝ × ℝ) (z : Fin n → ℝ × ℝ) : ℝ :=
  Instance.maximum (retainedTaggedVector t z)

lemma measurable_retainedMaximumAtTag : Measurable (fun p : (ℝ × ℝ) × (Fin n → ℝ × ℝ) => retainedMaximumAtTag p.1 p.2) :=
  Instance.measurable_maximum.comp measurable_retainedTaggedVector

lemma measurable_retainedMaximumAtTag_fixed (t : ℝ × ℝ) :
    Measurable (fun z : Fin n → ℝ × ℝ => retainedMaximumAtTag t z) := by
  simpa only [Function.comp_def,id_eq] using (measurable_retainedMaximumAtTag (n:=n)).comp
    ((measurable_const : Measurable (fun _ : Fin n → ℝ × ℝ => t)).prodMk measurable_id)

namespace Instance

noncomputable def retainedMaximumLaw (P : Instance n) (t : ℝ × ℝ) : Measure ℝ :=
  (P.retainedAtTag t).valuesLaw.map maximum

instance retainedMaximumLaw_probability (P : Instance n) (t : ℝ × ℝ) : IsProbabilityMeasure (P.retainedMaximumLaw t) :=
  Measure.isProbabilityMeasure_map measurable_maximum.aemeasurable

lemma retainedMaximum_measurePreserving (P : Instance n) (t : ℝ × ℝ) :
    MeasurePreserving (retainedMaximumAtTag t) P.taggedValuesLaw (P.retainedMaximumLaw t) :=
  (show MeasurePreserving maximum (P.retainedAtTag t).valuesLaw (P.retainedMaximumLaw t) from ⟨measurable_maximum,rfl⟩).comp
    (P.taggedRetainedValues_measurePreserving t)

lemma retainedMaximumLaw_Ioi (P : Instance n) (t : ℝ × ℝ) (b : ℝ) :
    (P.retainedMaximumLaw t).real (Ioi b)=
      ∫ z, (if b<retainedMaximumAtTag t z then (1:ℝ) else 0) ∂P.taggedValuesLaw := by
  have hMP := P.retainedMaximum_measurePreserving t
  have hMap := map_measureReal_apply (μ:=P.taggedValuesLaw) hMP.measurable (measurableSet_Ioi (a:=b))
  rw [hMP.map_eq] at hMap
  have hE : MeasurableSet {z | b<retainedMaximumAtTag (n:=n) t z} :=
    measurableSet_lt measurable_const (measurable_retainedMaximumAtTag_fixed t)
  have hI := integral_indicator_const (μ:=P.taggedValuesLaw) (1:ℝ) hE
  have hI' : (∫ z, (if b<retainedMaximumAtTag t z then (1:ℝ) else 0) ∂P.taggedValuesLaw)=
      P.taggedValuesLaw.real {z | b<retainedMaximumAtTag t z} := by
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using hI
  exact hMap.trans hI'.symm

lemma retainedMaximumLaw_Ici (P : Instance n) (t : ℝ × ℝ) (b : ℝ) :
    (P.retainedMaximumLaw t).real (Ici b)=
      ∫ z, (if b≤retainedMaximumAtTag t z then (1:ℝ) else 0) ∂P.taggedValuesLaw := by
  have hMP := P.retainedMaximum_measurePreserving t
  have hMap := map_measureReal_apply (μ:=P.taggedValuesLaw) hMP.measurable (measurableSet_Ici (a:=b))
  rw [hMP.map_eq] at hMap
  have hE : MeasurableSet {z | b≤retainedMaximumAtTag (n:=n) t z} :=
    measurableSet_le measurable_const (measurable_retainedMaximumAtTag_fixed t)
  have hI := integral_indicator_const (μ:=P.taggedValuesLaw) (1:ℝ) hE
  have hI' : (∫ z, (if b≤retainedMaximumAtTag t z then (1:ℝ) else 0) ∂P.taggedValuesLaw)=
      P.taggedValuesLaw.real {z | b≤retainedMaximumAtTag t z} := by
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using hI
  exact hMap.trans hI'.symm

lemma measurable_retainedMaximumLaw_Ioi (P : Instance n) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => (P.retainedMaximumLaw p.1).real (Ioi p.2)) := by
  let A := (ℝ × ℝ) × ℝ
  have hInput : Measurable (fun p : A × (Fin n → ℝ × ℝ) => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hMax : Measurable (fun p : A × (Fin n → ℝ × ℝ) => retainedMaximumAtTag p.1.1 p.2) :=
    by simpa only [Function.comp_def] using (measurable_retainedMaximumAtTag (n:=n)).comp hInput
  have hF : Measurable (fun p : A × (Fin n → ℝ × ℝ) => if p.1.2<retainedMaximumAtTag p.1.1 p.2 then (1:ℝ) else 0) :=
    measurable_const.ite (measurableSet_lt (measurable_snd.comp measurable_fst) hMax) measurable_const
  have hEq : (fun p : A => (P.retainedMaximumLaw p.1).real (Ioi p.2))=
      (fun p : A => ∫ z, (if p.2<retainedMaximumAtTag p.1 z then (1:ℝ) else 0) ∂P.taggedValuesLaw) :=
    funext (fun p => P.retainedMaximumLaw_Ioi p.1 p.2)
  rw [hEq]
  exact (hF.stronglyMeasurable.integral_prod_right' (ν:=P.taggedValuesLaw)).measurable

lemma measurable_retainedMaximumLaw_Ici (P : Instance n) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => (P.retainedMaximumLaw p.1).real (Ici p.2)) := by
  let A := (ℝ × ℝ) × ℝ
  have hInput : Measurable (fun p : A × (Fin n → ℝ × ℝ) => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hMax : Measurable (fun p : A × (Fin n → ℝ × ℝ) => retainedMaximumAtTag p.1.1 p.2) :=
    by simpa only [Function.comp_def] using (measurable_retainedMaximumAtTag (n:=n)).comp hInput
  have hF : Measurable (fun p : A × (Fin n → ℝ × ℝ) => if p.1.2≤retainedMaximumAtTag p.1.1 p.2 then (1:ℝ) else 0) :=
    measurable_const.ite (measurableSet_le (measurable_snd.comp measurable_fst) hMax) measurable_const
  have hEq : (fun p : A => (P.retainedMaximumLaw p.1).real (Ici p.2))=
      (fun p : A => ∫ z, (if p.2≤retainedMaximumAtTag p.1 z then (1:ℝ) else 0) ∂P.taggedValuesLaw) :=
    funext (fun p => P.retainedMaximumLaw_Ici p.1 p.2)
  rw [hEq]
  exact (hF.stronglyMeasurable.integral_prod_right' (ν:=P.taggedValuesLaw)).measurable

lemma retainedMaximumLaw_Ioi_values (P : Instance n) (t : ℝ × ℝ) (b : ℝ) :
    (P.retainedMaximumLaw t).real (Ioi b)=(P.retainedAtTag t).valuesLaw.real {y | b<maximum y} :=
  map_measureReal_apply (μ:=(P.retainedAtTag t).valuesLaw) measurable_maximum measurableSet_Ioi

lemma retainedMaximumLaw_Ici_values (P : Instance n) (t : ℝ × ℝ) (b : ℝ) :
    (P.retainedMaximumLaw t).real (Ici b)=(P.retainedAtTag t).valuesLaw.real {y | b≤maximum y} :=
  map_measureReal_apply (μ:=(P.retainedAtTag t).valuesLaw) measurable_maximum measurableSet_Ici

end Instance
end ProphetSecretary.Model
