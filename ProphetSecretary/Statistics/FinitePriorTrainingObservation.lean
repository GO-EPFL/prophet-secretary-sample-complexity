import ProphetSecretary.Statistics.FinitePriorExpectation
import ProphetSecretary.Statistics.FinitePriorPrefixSampling
import Mathlib.Probability.HasLaw

/-!
# The exact hidden-atom and visible-training law

The atom is retained only for analytical conditioning. The learner sees
the reconstructed training reservoir. Unused columns and the separate
ONLINE vector are integrated out by a proved product-coordinate map.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def trainingPriorLaw (F : FinitePrior n) (c : ℕ) :
    Measure (Fin F.size × Reservoir n c) :=
  ∑ θ : Fin F.size, F.weight θ • (Measure.dirac θ).prod ((F.offerInstance θ).reservoirLaw c)

instance trainingPriorLaw_probability (F : FinitePrior n) (c : ℕ) : IsProbabilityMeasure (F.trainingPriorLaw c) := by
  constructor
  simp only [trainingPriorLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,ENNReal.smul_one]
  exact_mod_cast F.weight_sum

def priorTrainingObservation (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) :
    Fin F.size × Reservoir n (trainingLength N b k) := (ω.1,F.observedTraining N b k ω)

lemma priorTrainingObservation_measurePreserving (F : FinitePrior n) (N b k : ℕ) :
    MeasurePreserving (F.priorTrainingObservation N b k) (F.law N)
      (F.trainingPriorLaw (trainingLength N b k)) := by
  let c := trainingLength N b k
  have hFn : F.priorTrainingObservation N b k=(fun ω : BaseWorld F N =>
      (ω.1,reservoirCoordinates.symm (prefixOnlineValues n N c (trainingLength_le N b k) ω.2).1)) := by
    funext ω
    change (ω.1,F.observedTraining N b k ω)=
      (ω.1,reservoirCoordinates.symm (prefixOnlineValues n N c (trainingLength_le N b k) ω.2).1)
    apply Prod.ext
    · rfl
    · rw [F.observedTraining_eq]
      rfl
  have hMeas : Measurable (F.priorTrainingObservation N b k) :=
    measurable_fst.prodMk ((measurable_reservoirFromObservation n N b k).comp (F.measurable_observe N b k))
  have hAtom (θ : Fin F.size) : MeasurePreserving (F.priorTrainingObservation N b k)
      (F.atomLaw N θ) ((Measure.dirac θ).prod ((F.offerInstance θ).reservoirLaw c)) := by
    have hFlat : MeasurePreserving (fun a : ValueArray n N =>
        (prefixOnlineValues n N c (trainingLength_le N b k) a).1)
        ((F.offerInstance θ).trainingCoordinateLaw (N+1)) ((F.offerInstance θ).trainingCoordinateLaw c) :=
      measurePreserving_fst.comp (prefixOnlineValues_measurePreserving (F.offerInstance θ) N c (trainingLength_le N b k))
    have hData := ((F.offerInstance θ).reservoirCoordinates_symm_measurePreserving c).comp hFlat
    rw [hFn]
    exact (MeasurePreserving.id (Measure.dirac θ)).prod hData
  refine ⟨hMeas,?_⟩
  simp only [law,trainingPriorLaw,Measure.map_finset_sum' hMeas.aemeasurable,Measure.map_smul]
  exact Finset.sum_congr rfl (fun θ _ => congrArg (fun μ => F.weight θ • μ) (hAtom θ).map_eq)

theorem integral_trainingPriorLaw (F : FinitePrior n) (c : ℕ) {f : Fin F.size × Reservoir n c → ℝ}
    (hf : Measurable f) (hInt : Integrable f (F.trainingPriorLaw c)) :
    (∫ p, f p ∂F.trainingPriorLaw c)=
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*(∫ y, f (θ,y) ∂(F.offerInstance θ).reservoirLaw c) := by
  have hEach := integrable_finsetSum_measure.mp hInt
  rw [trainingPriorLaw,integral_finsetSum_measure hEach]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro θ _
  congr 1
  have hTag : MeasurePreserving (Prod.mk θ) ((F.offerInstance θ).reservoirLaw c)
      ((Measure.dirac θ).prod ((F.offerInstance θ).reservoirLaw c)) :=
    ⟨measurable_const.prodMk measurable_id,(Measure.dirac_prod θ).symm⟩
  exact (hTag.hasLaw.integral_comp hf.aestronglyMeasurable).symm

end ProphetSecretary.Statistics.FinitePrior
