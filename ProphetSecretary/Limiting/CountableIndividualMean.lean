import ProphetSecretary.Limiting.CountableIndividualMap
import ProphetSecretary.Limiting.CountableDurationValueConstancy

/-!
# Mean contraction of one countable individual law

The mean lies in the supported convex hull and in the common offer cap.
Replacing that individual by its mean retains its identity and independent
arrival clock, every other marginal and the anonymous intensity.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def individualMean (B : CountableInstance) (i : ℕ) : ℝ :=
  ∫ x, x ∂(B.individuals i : Measure ℝ)

lemma individualMean_mem_cap (B : CountableInstance) (i : ℕ) :
    B.individualMean i ∈ Icc (0 : ℝ) B.cap := by
  have hSupp := (B.individuals i : Measure ℝ).support_subset_of_isClosed isClosed_Icc (B.individual_supported i)
  exact (convexHull_min hSupp (convex_Icc (0 : ℝ) (B.cap : ℝ))) (B.individual_mean_mem_support_hull i)

noncomputable def contractIndividual (B : CountableInstance) (i : ℕ) : CountableInstance :=
  B.mapIndividual i (fun _ => B.individualMean i) measurable_const
    (Eventually.of_forall (fun _ => B.individualMean_mem_cap i))

lemma contractIndividual_terminal (B : CountableInstance) (i : ℕ) :
    (B.contractIndividual i).terminal=B.terminal := rfl

lemma contractIndividual_cap (B : CountableInstance) (i : ℕ) :
    (B.contractIndividual i).cap=B.cap := rfl

lemma contractIndividual_intensity (B : CountableInstance) (i : ℕ) :
    (B.contractIndividual i).intensity=B.intensity := rfl

lemma contractIndividual_individual_law (B : CountableInstance) (i : ℕ) :
    ((B.contractIndividual i).individuals i : Measure ℝ)=Measure.dirac (B.individualMean i) := by
  simp only [contractIndividual,mapIndividual,updateIndividual,Function.update_self,ProbabilityMeasure.toMeasure_map]
  change Measure.map (fun _ : ℝ => B.individualMean i) (B.individuals i : Measure ℝ)=_
  simp only [Measure.map_const,measure_univ,one_smul]

lemma contractIndividual_other (B : CountableInstance) (i j : ℕ) (hji : j≠i) :
    (B.contractIndividual i).individuals j=B.individuals j := Function.update_of_ne hji _ _

theorem meanSubstitution_measurePreserving (B : CountableInstance) (i : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : CompleteWorld Seed => replaceIndividualValue i (v,B.individualMean i))
      (B.completeWorldLaw ν) ((B.contractIndividual i).completeWorldLaw ν) :=
  B.mapSingleIndividualWorld_measurePreserving i (fun _ => B.individualMean i) measurable_const
    (Eventually.of_forall (fun _ => B.individualMean_mem_cap i)) ν

end ProphetSecretary.Limiting.CountableInstance
