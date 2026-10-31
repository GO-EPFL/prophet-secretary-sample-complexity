import ProphetSecretary.Limiting.CountableIndividualChange
import ProphetSecretary.Limiting.CountableValueReplacement
import ProphetSecretary.Probability.InfiniteCoordinateKernel

/-!
# Conditional reconstruction of an individual in the full observation world

A fresh independent auxiliary sample and the displayed value reconstruct the
original marginal. The complete product law is preserved, including the
independent clocks, anonymous cloud and arbitrary policy seed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed U : Type*} [MeasurableSpace Seed] [MeasurableSpace U]

noncomputable def separateIndividualAuxiliary (v : CompleteWorld (Seed × U)) :
    BandConfigurations × (((ℕ → ℝ) × U) × ((ℕ → ℝ) × Seed)) :=
  (v.1,((v.2.1,v.2.2.2.2),(v.2.2.1,v.2.2.2.1)))

lemma separateIndividualAuxiliary_measurePreserving (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (ρ : Measure U) [IsProbabilityMeasure ρ] :
    MeasurePreserving separateIndividualAuxiliary (B.completeWorldLaw (ν.prod ρ))
      (B.bandConfigurationsLaw.prod ((B.individualValuesLaw.prod ρ).prod (individualClocksLaw.prod ν))) := by
  have h₁ := (MeasurePreserving.id B.individualValuesLaw).prod
    ((measurePreserving_prodAssoc individualClocksLaw ν ρ).symm MeasurableEquiv.prodAssoc)
  have h₂ := (measurePreserving_prodAssoc B.individualValuesLaw (individualClocksLaw.prod ν) ρ).symm MeasurableEquiv.prodAssoc
  have h₃ := Model.measurePreserving_swap_last B.individualValuesLaw (individualClocksLaw.prod ν) ρ
  exact (MeasurePreserving.id B.bandConfigurationsLaw).prod (h₃.comp (h₂.comp h₁))

noncomputable def recoverIndividualWorld (i : ℕ) (F : ℝ × U → ℝ)
    (v : CompleteWorld (Seed × U)) : CompleteWorld Seed :=
  (v.1,(Function.update v.2.1 i (F (v.2.1 i,v.2.2.2.2)),(v.2.2.1,v.2.2.2.1)))

lemma recoverIndividualWorld_measurePreserving (B : CountableInstance) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (ρ : Measure U) [IsProbabilityMeasure ρ]
    {F : ℝ × U → ℝ} (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ)) :
    MeasurePreserving (recoverIndividualWorld i F) ((B.updateIndividual i q hSupport).completeWorldLaw (ν.prod ρ))
      (B.completeWorldLaw ν) := by
  let D := B.updateIndividual i q hSupport
  have hFD : MeasurePreserving F ((D.individuals i : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ) := by
    simpa only [D,updateIndividual,Function.update_self] using hF
  have hCoordinate : MeasurePreserving (fun z : (ℕ → ℝ) × U => Function.update z.1 i (F (z.1 i,z.2)))
      (D.individualValuesLaw.prod ρ) B.individualValuesLaw := by
    have h := ProphetSecretary.Probability.infinite_randomCoordinate_measurePreserving
      (fun j => (D.individuals j : Measure ℝ)) i ρ (B.individuals i : Measure ℝ) hFD
    have hFamily : Function.update (fun j => (D.individuals j : Measure ℝ)) i (B.individuals i : Measure ℝ)=
        (fun j => (B.individuals j : Measure ℝ)) := by
      funext j
      by_cases hj : j=i
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hj,D,updateIndividual]
    rw [hFamily] at h
    exact h
  have hOuter := (MeasurePreserving.id B.bandConfigurationsLaw).prod
    (hCoordinate.prod (MeasurePreserving.id (individualClocksLaw.prod ν)))
  exact hOuter.comp (D.separateIndividualAuxiliary_measurePreserving ν ρ)

lemma individual_seedAuxiliary_measurePreserving (B : CountableInstance) (i : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (ρ : Measure U) [IsProbabilityMeasure ρ] :
    MeasurePreserving (fun v : CompleteWorld (Seed × U) => (v.2.1 i,v.2.2.2.2))
      (B.completeWorldLaw (ν.prod ρ)) ((B.individuals i : Measure ℝ).prod ρ) := by
  have hCoordinates := (B.individualValue_measurePreserving i).prod (MeasurePreserving.id ρ)
  have hDrop : MeasurePreserving (fun z : BandConfigurations × (((ℕ → ℝ) × U) × ((ℕ → ℝ) × Seed)) => z.2.1)
      (B.bandConfigurationsLaw.prod ((B.individualValuesLaw.prod ρ).prod (individualClocksLaw.prod ν)))
      (B.individualValuesLaw.prod ρ) := measurePreserving_fst.comp measurePreserving_snd
  exact hCoordinates.comp (hDrop.comp (B.separateIndividualAuxiliary_measurePreserving ν ρ))

end ProphetSecretary.Limiting.CountableInstance
