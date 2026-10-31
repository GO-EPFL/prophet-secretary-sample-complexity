import ProphetSecretary.Statistics.FinitePriorAuxiliary
import Mathlib.Probability.HasLaw

/-!
# Exact expectations in the actual finite-prior experiment

A common independent auxiliary law remains a product factor at every prior
atom. Integrability under the actual mixture suffices for the finite sum
identity; no boundedness on impossible raw observations is assumed.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

lemma auxiliaryWorldLaw_eq_sum (F : FinitePrior n) (N : ℕ)
    (ν : Measure Aux) [IsProbabilityMeasure ν] :
    F.auxiliaryWorldLaw N ν=∑ θ : Fin F.size, F.weight θ • ((F.atomLaw N θ).prod ν) := by
  change (∑ θ : Fin F.size, F.weight θ • F.atomLaw N θ).prod ν=_
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype]
  simp only [Measure.prod_smul_left]

lemma atomAuxiliary_insert_measurePreserving (F : FinitePrior n) (N : ℕ)
    (ν : Measure Aux) [IsProbabilityMeasure ν] (θ : Fin F.size) :
    MeasurePreserving (fun z : ValueArray n N × Aux => ((θ,z.1),z.2))
      (((F.offerInstance θ).trainingCoordinateLaw (N+1)).prod ν) ((F.atomLaw N θ).prod ν) := by
  let μ := (F.offerInstance θ).trainingCoordinateLaw (N+1)
  have hTag : MeasurePreserving (Prod.mk θ) (μ.prod ν) ((Measure.dirac θ).prod (μ.prod ν)) :=
    ⟨measurable_const.prodMk measurable_id,(Measure.dirac_prod θ).symm⟩
  exact ((measurePreserving_prodAssoc (Measure.dirac θ) μ ν).symm MeasurableEquiv.prodAssoc).comp hTag

theorem integral_auxiliaryWorldLaw (F : FinitePrior n) (N : ℕ)
    (ν : Measure Aux) [IsProbabilityMeasure ν] {f : BaseWorld F N × Aux → ℝ}
    (hf : Measurable f) (hInt : Integrable f (F.auxiliaryWorldLaw N ν)) :
    (∫ w, f w ∂F.auxiliaryWorldLaw N ν)=
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        (∫ z : ValueArray n N × Aux, f ((θ,z.1),z.2)
          ∂((F.offerInstance θ).trainingCoordinateLaw (N+1)).prod ν) := by
  have hEach := integrable_finsetSum_measure.mp ((F.auxiliaryWorldLaw_eq_sum N ν) ▸ hInt)
  rw [F.auxiliaryWorldLaw_eq_sum,integral_finsetSum_measure hEach]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro θ _
  congr 1
  exact ((F.atomAuxiliary_insert_measurePreserving N ν θ).hasLaw.integral_comp hf.aestronglyMeasurable).symm

end ProphetSecretary.Statistics.FinitePrior
