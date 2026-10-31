import ProphetSecretary.Model.OuterRetainedMaximum
import ProphetSecretary.Model.OuterRetentionMean

/-!
# Conditional retained maxima without a boundedness assumption

The original integrable maximum dominates the retained maximum on the fresh
independent offer/tag factor. This permits conditioning at an arbitrary
measurable cutoff even for unbounded offers.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model.Instance
variable {n : ℕ}

lemma retainedAtTag_expectedMaximum_eq_integral (P : Instance n) (t : ℝ × ℝ) :
    (P.retainedAtTag t).expectedMaximum=∫ z, retainedMaximumAtTag t z ∂P.taggedValuesLaw := by
  have hRet := P.taggedRetainedValues_measurePreserving t
  have hMap := integral_map (μ:=P.taggedValuesLaw) hRet.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
  rw [hRet.map_eq] at hMap
  exact hMap

lemma measurable_retainedAtTag_expectedMaximum (P : Instance n) :
    Measurable (fun t : ℝ × ℝ => (P.retainedAtTag t).expectedMaximum) := by
  have hEq : (fun t : ℝ × ℝ => (P.retainedAtTag t).expectedMaximum)=
      (fun t => ∫ z, retainedMaximumAtTag t z ∂P.taggedValuesLaw) :=
    funext (fun t => P.retainedAtTag_expectedMaximum_eq_integral t)
  rw [hEq]
  exact ((measurable_retainedMaximumAtTag (n:=n)).stronglyMeasurable.integral_prod_right' (ν:=P.taggedValuesLaw)).measurable

lemma retainedMaximumAtTag_integrable_product (P : Instance n)
    (hP : Integrable maximum P.valuesLaw)
    {D : Type*} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {T : D → ℝ × ℝ} (hT : Measurable T) :
    Integrable (fun p : D × (Fin n → ℝ × ℝ) => retainedMaximumAtTag (T p.1) p.2) (μ.prod P.taggedValuesLaw) := by
  have hOrig : Integrable (fun z : Fin n → ℝ × ℝ => maximum (fun i => (z i).1)) P.taggedValuesLaw :=
    P.taggedValues_projection_measurePreserving.integrable_comp_of_integrable hP
  have hDom := hOrig.comp_snd μ
  have hMeas : Measurable (fun p : D × (Fin n → ℝ × ℝ) => retainedMaximumAtTag (T p.1) p.2) := by
    simpa only [Function.comp_def] using (measurable_retainedMaximumAtTag (n:=n)).comp
      ((hT.comp measurable_fst).prodMk measurable_snd)
  apply hDom.mono' hMeas.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖maximum (retainedTaggedVector (T p.1) p.2)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (maximum_nonnegative _)]
    exact maximum_retainedAtTag_le _ _

lemma integrable_retainedAtTag_expectedMaximum (P : Instance n)
    (hP : Integrable maximum P.valuesLaw)
    {D : Type*} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {T : D → ℝ × ℝ} (hT : Measurable T) :
    Integrable (fun d => (P.retainedAtTag (T d)).expectedMaximum) μ := by
  apply Integrable.of_bound ((P.measurable_retainedAtTag_expectedMaximum.comp hT).aestronglyMeasurable) P.expectedMaximum
  exact Eventually.of_forall fun d => by
    change ‖(P.retainedAtTag (T d)).expectedMaximum‖≤P.expectedMaximum
    rw [Real.norm_eq_abs,abs_of_nonneg (P.retainedAtTag _).expectedMaximum_nonnegative]
    exact P.retainedAtTag_expectedMaximum_le hP _

/-- Conditional expectation of the fresh retained maximum given the actual cutoff. -/
theorem retainedMaximumAtTag_condExp (P : Instance n)
    (hP : Integrable maximum P.valuesLaw)
    {D : Type*} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {T : D → ℝ × ℝ} (hT : Measurable T) :
    (μ.prod P.taggedValuesLaw)[(fun p => retainedMaximumAtTag (T p.1) p.2)|
      MeasurableSpace.comap (fun p : D × (Fin n → ℝ × ℝ) => T p.1) inferInstance] =ᵐ[μ.prod P.taggedValuesLaw]
      (fun p => (P.retainedAtTag (T p.1)).expectedMaximum) := by
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hTM : MeasurePreserving T μ (μ.map T) := ⟨hT,rfl⟩
  have hPair : MeasurePreserving (fun p : D × (Fin n → ℝ × ℝ) => (T p.1,p.2))
      (μ.prod P.taggedValuesLaw) ((μ.map T).prod P.taggedValuesLaw) :=
    hTM.prod (MeasurePreserving.id P.taggedValuesLaw)
  have hFI := P.retainedMaximumAtTag_integrable_product hP (μ.map T) measurable_id
  have h := ProphetSecretary.Probability.condExp_productPair (μ.map T) P.taggedValuesLaw
    (μ.prod P.taggedValuesLaw) hPair (measurable_retainedMaximumAtTag (n:=n)) hFI
  apply h.trans
  exact Eventually.of_forall fun p => (P.retainedAtTag_expectedMaximum_eq_integral (T p.1)).symm

end ProphetSecretary.Model.Instance
