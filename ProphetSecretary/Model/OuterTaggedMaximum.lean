import ProphetSecretary.Model.OuterRetentionMean
import ProphetSecretary.Probability.TaggedOrder
import ProphetSecretary.Probability.OrderCDFUniform

/-!
# The actual lexicographically maximal tagged offer

A nonempty finite family has a genuine tagged maximum, selected from the
observed offers. Its CDF is exactly the product void probability used for
retention. Its tag lies in the open unit interval almost surely, including
when every numerical offer is zero.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma taggedAbove_iff_lex_lt (t z : ℝ × ℝ) :
    taggedAbove t z ↔ (toLex t : TaggedValue)<toLex z := by
  rw [Prod.Lex.lt_iff]
  rfl

lemma outerOfferIndices_nonempty (hn : 0<n) : (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0,hn⟩,Finset.mem_univ _⟩

noncomputable def outerTaggedMaximum (hn : 0<n) (z : Fin n → ℝ × ℝ) : TaggedValue :=
  Finset.univ.sup' (outerOfferIndices_nonempty hn) (fun i => toLex (z i))

lemma measurable_outerTaggedMaximum (hn : 0<n) : Measurable (outerTaggedMaximum hn) := by
  have h := Finset.measurable_sup' (outerOfferIndices_nonempty hn)
    (fun i _ => measurable_toTaggedValue.comp (measurable_pi_apply i))
  convert h using 1
  funext z
  simp only [outerTaggedMaximum,Finset.sup'_apply,Function.comp_def]

namespace Instance

noncomputable def outerTaggedMaximumLaw (P : Instance n) (hn : 0<n) : Measure TaggedValue :=
  P.taggedValuesLaw.map (outerTaggedMaximum hn)

instance outerTaggedMaximumLaw_probability (P : Instance n) (hn : 0<n) : IsProbabilityMeasure (P.outerTaggedMaximumLaw hn) :=
  Measure.isProbabilityMeasure_map (measurable_outerTaggedMaximum hn).aemeasurable

lemma outerTaggedMaximum_tag_mem_open_unit (P : Instance n) (hn : 0<n) :
    ∀ᵐ z ∂P.outerTaggedMaximumLaw hn, (ofLex z).2∈Ioo (0:ℝ) 1 := by
  have hTagMeas : Measurable (fun z : TaggedValue => (ofLex z).2) := measurable_snd.comp measurable_ofTaggedValue
  apply (ae_map_iff (measurable_outerTaggedMaximum hn).aemeasurable (measurableSet_Ioo.preimage hTagMeas)).mpr
  have hAll : ∀ᵐ z ∂P.taggedValuesLaw, ∀ i : Fin n, (z i).2∈Ioo (0:ℝ) 1 :=
    ae_all_iff.mpr fun i => ((measurePreserving_snd (μ:=P.law i) (ν:=uniformClock)).comp
      (measurePreserving_eval (fun j : Fin n => (P.law j).prod uniformClock) i)).quasiMeasurePreserving.ae
        ProphetSecretary.Probability.uniformClock_mem_open_unit
  filter_upwards [hAll] with z hz
  obtain ⟨i,_,hEq⟩ := Finset.exists_mem_eq_sup' (outerOfferIndices_nonempty hn) (fun j => (toLex (z j) : TaggedValue))
  change (ofLex (Finset.univ.sup' (outerOfferIndices_nonempty hn) (fun j => (toLex (z j) : TaggedValue)))).2∈Ioo (0:ℝ) 1
  rw [hEq]
  exact hz i

/-- The product CDF G in the cutoff proof is the actual tagged-maximum CDF. -/
lemma outerTaggedMaximum_cdf_eq_void (P : Instance n) (hn : 0<n) (t : TaggedValue) :
    orderCDF (P.outerTaggedMaximumLaw hn) t=P.taggedVoidProbability (ofLex t) := by
  have hIic : MeasurableSet (Iic t) := measurableSet_taggedValue_le.preimage (measurable_id.prodMk measurable_const)
  have hMap := map_measureReal_apply (μ:=P.taggedValuesLaw) (measurable_outerTaggedMaximum hn) hIic
  change (P.taggedValuesLaw.map (outerTaggedMaximum hn)).real (Iic t)=_
  rw [hMap]
  have hSet : outerTaggedMaximum hn ⁻¹' Iic t=taggedVoidEvent (ofLex t) := by
    ext z
    simp only [Set.mem_preimage,Set.mem_Iic,outerTaggedMaximum,Finset.sup'_le_iff,Finset.mem_univ,forall_true_left,
      taggedVoidEvent,Set.mem_setOf_eq]
    apply forall_congr'
    intro i
    rw [taggedAbove_iff_lex_lt]
    change (toLex (z i) : TaggedValue)≤t ↔ ¬t<toLex (z i)
    exact not_lt.symm
  rw [hSet,P.taggedVoidEvent_probability]

end Instance
end ProphetSecretary.Model
