import ProphetSecretary.Statistics.PlannerTransitionLaw
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real expectations under the planner kernel

The direct sampler identifies the kernel as a probability law. A bounded
measurable payoff can therefore be integrated branch by branch against the
explicit density; no integrability premise about the planner is assumed.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

lemma integral_plannerKernelLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i)
    (f : Fin n × ℝ × Finset (Fin n) → ℝ) (hf : Measurable f)
    (hbound : ∀ x, |f x| ≤ 1) :
    (∫ x, f x ∂plannerKernelLaw A p) =
      ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
        ∫ s, plannerKernelDensity A p i B s * f (i,s,B) ∂Instance.uniformClock := by
  letI : IsProbabilityMeasure (plannerKernelLaw A p) := by
    rw [← plannerTransitionLaw_eq_kernelLaw A p hA hp]
    infer_instance
  have hI : Integrable f (plannerKernelLaw A p) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  let ν : Fin n → Finset (Fin n) → Measure (Fin n × ℝ × Finset (Fin n)) := fun i B =>
    (Instance.uniformClock.withDensity (fun s => ENNReal.ofReal (plannerKernelDensity A p i B s))).map
      (fun s => (i,s,B))
  have houter (i : Fin n) (hi : i ∈ A) : Integrable f (∑ B ∈ (A.erase i).powerset, ν i B) := by
    apply hI.mono_measure
    change (∑ B ∈ (A.erase i).powerset, ν i B) ≤ ∑ j ∈ A, ∑ B ∈ (A.erase j).powerset, ν j B
    exact Finset.single_le_sum
      (f := fun j : Fin n => ∑ B ∈ (A.erase j).powerset, ν j B)
      (fun j _ => Measure.zero_le _) hi
  have hinner (i : Fin n) (hi : i ∈ A) (B : Finset (Fin n))
      (hB : B ∈ (A.erase i).powerset) : Integrable f (ν i B) := by
    apply (houter i hi).mono_measure
    exact Finset.single_le_sum (f := fun C : Finset (Fin n) => ν i C)
      (fun C _ => Measure.zero_le _) hB
  change (∫ x, f x ∂∑ i ∈ A, ∑ B ∈ (A.erase i).powerset, ν i B) = _
  rw [integral_finsetSum_measure houter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum_measure (hinner i hi)]
  apply Finset.sum_congr rfl
  intro B hB
  have hmap : Measurable (fun s : ℝ => (i,s,B)) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  dsimp [ν]
  rw [integral_map hmap.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by unfold plannerKernelDensity; fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  have hsupp : ∀ᵐ s ∂Instance.uniformClock, s ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [hsupp] with s hs
  rw [ENNReal.toReal_ofReal (plannerKernelDensity_nonneg A p (fun j hj => (hp j hj).le)
    hi (Finset.mem_powerset.mp hB) hs), smul_eq_mul]

end ProphetSecretary.Statistics
