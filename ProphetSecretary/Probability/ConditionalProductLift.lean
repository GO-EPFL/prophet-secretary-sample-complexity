import ProphetSecretary.Probability.ProductConditioning

/-!
# Adding independent auxiliary randomness to a conditional projection

An unobserved independent second coordinate does not alter the posterior. The
identity is proved by set-integral characterization, with no independence field.
-/

open MeasureTheory Set
namespace ProphetSecretary.Probability
variable {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem condExp_prod_lift {m : MeasurableSpace A} (hm : m≤mA)
    {f : A → ℝ} (hf : Integrable f μ) :
    letI : MeasurableSpace A := mA
    (fun z : A × B => μ[f|m] z.1) =ᵐ[μ.prod ν]
      (μ.prod ν)[(fun z => f z.1)|m.comap Prod.fst] := by
  letI : MeasurableSpace A := mA
  have hm' : m.comap (Prod.fst : A × B → A)≤mA.prod mB :=
    (MeasurableSpace.comap_mono hm).trans measurable_fst.comap_le
  have hG : StronglyMeasurable[m.comap (Prod.fst : A × B → A)]
      (fun z : A × B => μ[f|m] z.1) := by
    have hfst : @Measurable (A×B) A (m.comap Prod.fst) m Prod.fst := Measurable.of_comap_le le_rfl
    exact (stronglyMeasurable_condExp (μ:=μ) (m:=m) (f:=f)).comp_measurable hfst
  have hGI : Integrable (fun z : A × B => μ[f|m] z.1) (μ.prod ν) := integrable_condExp.comp_fst ν
  have hFI : Integrable (fun z : A × B => f z.1) (μ.prod ν) := hf.comp_fst ν
  apply ae_eq_condExp_of_forall_setIntegral_eq hm' hFI (fun _ _ _ => hGI.integrableOn) ?_ hG.aestronglyMeasurable
  intro E hE _
  obtain ⟨s,hs,he⟩ := MeasurableSpace.measurableSet_comap.mp hE
  have hset : E=s×ˢ(univ : Set B) := by
    rw [←he]
    ext z
    simp
  rw [hset,setIntegral_prod _ hGI.integrableOn,setIntegral_prod _ hFI.integrableOn]
  simp only [Measure.restrict_univ,integral_const,probReal_univ,one_smul]
  exact setIntegral_condExp hm hf hs

end ProphetSecretary.Probability
