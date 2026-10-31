import ProphetSecretary.Model.OuterRetention
import ProphetSecretary.Probability.ProductConditioning

/-!
# The actual retained product law conditional on outer data

An arbitrary measurable cutoff is computed from independent outer data. The
fresh offer/tag vector is a separate product factor. Conditional expectation
identifies its transformed law with the stated retained product instance, even
when the cutoff has atoms and without observing any fresh online coordinates.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def retainedTaggedVector (t : ℝ × ℝ) (z : Fin n → ℝ × ℝ) : Fin n → ℝ :=
  fun i => retainAboveTag t (z i)

lemma measurable_retainedTaggedVector : Measurable (fun p : (ℝ × ℝ) × (Fin n → ℝ × ℝ) => retainedTaggedVector p.1 p.2) :=
  measurable_pi_lambda _ (fun i => measurable_retainAboveTag.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

/-- Actual conditional distribution of fresh retained values given the realized
cutoff. The measure-preserving independent-cutoff map is constructed in the proof. -/
theorem Instance.retainedTaggedVector_condExp (P : Instance n)
    {D : Type*} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {T : D → ℝ × ℝ} (hT : Measurable T)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖≤C) :
    (μ.prod P.taggedValuesLaw)[(fun p => f (retainedTaggedVector (T p.1) p.2))|
      MeasurableSpace.comap (fun p : D × (Fin n → ℝ × ℝ) => T p.1) inferInstance] =ᵐ[μ.prod P.taggedValuesLaw]
      (fun p => ∫ y, f y ∂(P.retainedAtTag (T p.1)).valuesLaw) := by
  let F : (ℝ × ℝ) × (Fin n → ℝ × ℝ) → ℝ := fun p => f (retainedTaggedVector p.1 p.2)
  have hFm : Measurable F := hf.comp measurable_retainedTaggedVector
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hFI : Integrable F ((μ.map T).prod P.taggedValuesLaw) := Integrable.of_bound hFm.aestronglyMeasurable C
    (Eventually.of_forall fun p => hC _)
  have hTM : MeasurePreserving T μ (μ.map T) := ⟨hT,rfl⟩
  have hPair : MeasurePreserving (fun p : D × (Fin n → ℝ × ℝ) => (T p.1,p.2))
      (μ.prod P.taggedValuesLaw) ((μ.map T).prod P.taggedValuesLaw) :=
    hTM.prod (MeasurePreserving.id P.taggedValuesLaw)
  have h := ProphetSecretary.Probability.condExp_productPair (μ.map T) P.taggedValuesLaw
    (μ.prod P.taggedValuesLaw) hPair hFm hFI
  apply h.trans
  exact Eventually.of_forall fun p => by
    have hRet := P.taggedRetainedValues_measurePreserving (T p.1)
    have hMap := integral_map (μ:=P.taggedValuesLaw) hRet.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hRet.map_eq] at hMap
    exact hMap.symm

end ProphetSecretary.Model
