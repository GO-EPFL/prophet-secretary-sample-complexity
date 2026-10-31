import ProphetSecretary.Limiting.CountableIndividualChange
import ProphetSecretary.Limiting.CountableValueReplacement

/-!
# Measurable transport of one full individual value

A measurable map changes only the chosen value law. The actual world map
retains its identity, clock, all other observations, anonymous configuration
and independent seed. Its pushforward is proved from the infinite-product
coordinate map theorem.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def mapSingleIndividualWorld (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  replaceIndividualValue i (v,g (v.2.1 i))

noncomputable def mapIndividual (B : CountableInstance) (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x ∈ Icc (0 : ℝ) B.cap) : CountableInstance :=
  B.updateIndividual i ((B.individuals i).map hg.aemeasurable)
    ((ae_map_iff hg.aemeasurable measurableSet_Icc).mpr hSupport)

lemma mapIndividual_valuesLaw (B : CountableInstance) (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x ∈ Icc (0 : ℝ) B.cap) :
    MeasurePreserving (fun z : ℕ → ℝ => Function.update z i (g (z i)))
      B.individualValuesLaw (B.mapIndividual i g hg hSupport).individualValuesLaw := by
  let f : ℕ → ℝ → ℝ := fun j => if j=i then g else id
  have hf : ∀ j, Measurable (f j) := by
    intro j
    by_cases hj : j=i
    · simpa only [f,if_pos hj] using hg
    · simpa only [f,if_neg hj] using (measurable_id : Measurable (id : ℝ → ℝ))
  have hFun : (fun z : ℕ → ℝ => fun j => f j (z j))=(fun z => Function.update z i (g (z i))) := by
    funext z j
    by_cases hj : j=i
    · subst j
      simp only [f,if_pos rfl,Function.update_self]
    · simp only [f,if_neg hj,Function.update_of_ne hj,id_eq]
  have hm : Measurable (fun z : ℕ → ℝ => Function.update z i (g (z i))) := by
    rw [← hFun]
    exact measurable_pi_lambda _ (fun j => (hf j).comp (measurable_pi_apply j))
  refine ⟨hm,?_⟩
  change Measure.map _ (Measure.infinitePi (fun j => (B.individuals j : Measure ℝ)))=Measure.infinitePi _
  rw [← hFun,Measure.infinitePi_map_pi _ hf]
  congr 1
  funext j
  by_cases hj : j=i
  · subst j
    simp only [f,if_pos rfl,mapIndividual,updateIndividual,Function.update_self]
    rfl
  · simp only [f,if_neg hj,mapIndividual,updateIndividual,Function.update_of_ne hj,Measure.map_id]

variable [MeasurableSpace Seed]

lemma measurable_mapSingleIndividualWorld (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (mapSingleIndividualWorld (Seed := Seed) i g) :=
  (measurable_replaceIndividualValue i).comp (measurable_id.prodMk
    (hg.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))))

theorem mapSingleIndividualWorld_measurePreserving (B : CountableInstance) (i : ℕ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x ∈ Icc (0 : ℝ) B.cap)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (mapSingleIndividualWorld i g) (B.completeWorldLaw ν)
      ((B.mapIndividual i g hg hSupport).completeWorldLaw ν) :=
  (MeasurePreserving.id B.bandConfigurationsLaw).prod
    ((B.mapIndividual_valuesLaw i g hg hSupport).prod (MeasurePreserving.id (individualClocksLaw.prod ν)))

end ProphetSecretary.Limiting.CountableInstance
