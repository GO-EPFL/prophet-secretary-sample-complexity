import ProphetSecretary.Limiting.CountableValueReplacement
import ProphetSecretary.Limiting.CountableReachValue
import Mathlib.Probability.Independence.Integration

/-!
# Fixed individual replacement and the erased value

The world with a fixed replacement value is independent of the original
candidate value. This follows from actual infinite-product erasure, retaining
the candidate clock, every other offer and the auxiliary random seed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

lemma replaceIndividualValue_fixed_independent (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) (x : ℝ) :
    IndepFun (fun v : CompleteWorld Seed => replaceIndividualValue i (v,x))
      (fun v => v.2.1 i) (B.completeWorldLaw ν) := by
  have hM : Measurable (fun v : CompleteWorld Seed => replaceIndividualValue i (v,x)) :=
    (measurable_replaceIndividualValue i).comp (measurable_id.prodMk measurable_const)
  have h := (eraseIndividualValue_independent B ν i).comp hM measurable_id
  have hEq : (fun v : CompleteWorld Seed => replaceIndividualValue i (eraseIndividualValue i v,x))=
      (fun v => replaceIndividualValue i (v,x)) := by
    funext v
    simp only [replaceIndividualValue,eraseIndividualValue,Function.update_idem]
  change IndepFun (fun v : CompleteWorld Seed => replaceIndividualValue i (eraseIndividualValue i v,x))
    (fun v => v.2.1 i) (B.completeWorldLaw ν) at h
  rw [hEq] at h
  exact h

lemma integral_replaced_observable_mul_value (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) (x : ℝ)
    (f : CompleteWorld Seed → ℝ) (hf : Measurable f) :
    (∫ v, f (replaceIndividualValue i (v,x))*v.2.1 i ∂B.completeWorldLaw ν)=
      (∫ v, f (replaceIndividualValue i (v,x)) ∂B.completeWorldLaw ν)*
        (∫ y, y ∂(B.individuals i : Measure ℝ)) := by
  have hF : Measurable (fun v : CompleteWorld Seed => f (replaceIndividualValue i (v,x))) :=
    hf.comp ((measurable_replaceIndividualValue i).comp (measurable_id.prodMk measurable_const))
  have hX : Measurable (fun v : CompleteWorld Seed => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have h := ((replaceIndividualValue_fixed_independent B ν i x).comp hf measurable_id).integral_fun_mul_eq_mul_integral
    hF.aestronglyMeasurable hX.aestronglyMeasurable
  have hXi : MeasurePreserving (fun v : CompleteWorld Seed => v.2.1 i)
      (B.completeWorldLaw ν) (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  have hMean := integral_map hXi.measurable.aemeasurable
    (measurable_id.aestronglyMeasurable : AEStronglyMeasurable (fun y : ℝ => y) (Measure.map (fun v : CompleteWorld Seed => v.2.1 i) (B.completeWorldLaw ν)))
  rw [hXi.map_eq] at hMean
  exact h.trans (congrArg (fun z : ℝ => (∫ v, f (replaceIndividualValue i (v,x)) ∂B.completeWorldLaw ν)*z) hMean.symm)

end ProphetSecretary.Limiting.CountableInstance
