import ProphetSecretary.Probability.TaggedOrder
import ProphetSecretary.Probability.OrderCDFUniform
import ProphetSecretary.Probability.CDFQuantileBracket
import Mathlib.Topology.Order.IntermediateValue

/-!
# Filling numerical CDF jumps with continuous tags

Open-unit tags identify the vertical endpoint CDFs with the numerical open and
closed CDFs. Continuous variation along each tag interval therefore attains every
interior probability level, even at atoms. The general ordered transform then
has the actual uniform law.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Probability

noncomputable def taggedNumericLaw (μ : Measure TaggedValue) : Measure ℝ :=
  μ.map (fun z => (ofLex z).1)

lemma measurable_taggedNumeric : Measurable (fun z : TaggedValue => (ofLex z).1) :=
  measurable_fst.comp measurable_ofTaggedValue

instance taggedNumericLaw_probability (μ : Measure TaggedValue) [IsProbabilityMeasure μ] : IsProbabilityMeasure (taggedNumericLaw μ) :=
  Measure.isProbabilityMeasure_map measurable_taggedNumeric.aemeasurable

lemma tagged_orderCDF_zero (μ : Measure TaggedValue) [IsProbabilityMeasure μ]
    (hTag : ∀ᵐ z ∂μ, (ofLex z).2∈Ioo (0:ℝ) 1) (x : ℝ) :
    orderCDF μ (toLex (x,0))=(taggedNumericLaw μ).real (Iio x) := by
  have hMap := map_measureReal_apply (μ:=μ) measurable_taggedNumeric (measurableSet_Iio (a:=x))
  have hEq : Iic (toLex (x,0) : TaggedValue) =ᵐ[μ] (fun z : TaggedValue => (ofLex z).1) ⁻¹' Iio x := by
    filter_upwards [hTag] with z hz
    apply propext
    change z≤(toLex (x,0) : TaggedValue) ↔ (ofLex z).1<x
    rw [Prod.Lex.le_iff]
    change ((ofLex z).1<x ∨ (ofLex z).1=x ∧ (ofLex z).2≤0) ↔ (ofLex z).1<x
    constructor
    · rintro (h|⟨_,h⟩)
      · exact h
      · linarith only [h,hz.1]
    · exact Or.inl
  exact (measureReal_congr hEq).trans hMap.symm

lemma tagged_orderCDF_one (μ : Measure TaggedValue) [IsProbabilityMeasure μ]
    (hTag : ∀ᵐ z ∂μ, (ofLex z).2∈Ioo (0:ℝ) 1) (x : ℝ) :
    orderCDF μ (toLex (x,1))=(taggedNumericLaw μ).real (Iic x) := by
  have hMap := map_measureReal_apply (μ:=μ) measurable_taggedNumeric (measurableSet_Iic (a:=x))
  have hEq : Iic (toLex (x,1) : TaggedValue) =ᵐ[μ] (fun z : TaggedValue => (ofLex z).1) ⁻¹' Iic x := by
    filter_upwards [hTag] with z hz
    apply propext
    change z≤(toLex (x,1) : TaggedValue) ↔ (ofLex z).1≤x
    rw [Prod.Lex.le_iff]
    change ((ofLex z).1<x ∨ (ofLex z).1=x ∧ (ofLex z).2≤1) ↔ (ofLex z).1≤x
    constructor
    · rintro (h|⟨h,_⟩)
      · exact h.le
      · exact h.le
    · intro h
      rcases lt_or_eq_of_le h with h|h
      · exact Or.inl h
      · exact Or.inr ⟨h,hz.2.le⟩
  exact (measureReal_congr hEq).trans hMap.symm

/-- Continuous tag slices attain every numerical CDF jump interval. -/
theorem tagged_orderCDF_uniform (μ : Measure TaggedValue) [IsProbabilityMeasure μ]
    (hTag : ∀ᵐ z ∂μ, (ofLex z).2∈Ioo (0:ℝ) 1)
    (hVertical : ∀ x : ℝ, ContinuousOn (fun u : ℝ => orderCDF μ (toLex (x,u))) (Icc (0:ℝ) 1)) :
    MeasurePreserving (orderCDF μ) μ Model.Instance.uniformClock := by
  apply orderCDF_measurePreserving_uniform μ measurableSet_taggedValue_le
  intro q hq
  obtain ⟨x,hLeft,hRight,_⟩ := exists_cdf_probability_bracket (taggedNumericLaw μ) hq
  have hEnds : q∈Icc (orderCDF μ (toLex (x,0))) (orderCDF μ (toLex (x,1))) := by
    rw [tagged_orderCDF_zero μ hTag,tagged_orderCDF_one μ hTag]
    exact ⟨hLeft,hRight⟩
  obtain ⟨u,hu,hEq⟩ := intermediate_value_Icc zero_le_one (hVertical x) hEnds
  exact ⟨toLex (x,u),hEq⟩

end ProphetSecretary.Probability
