import ProphetSecretary.Model.Independence
import Mathlib.Probability.Independence.InfinitePi

/-!
# Erasing a coordinate of an infinite independent product

The erased vector is measurable with respect to the sigma-algebra generated
by all the other coordinates. Independence is derived from the actual product
law and disjoint coordinate sigma-algebras; it is not an execution hypothesis.
The index type need not be finite or countable.
-/

open MeasureTheory ProbabilityTheory Set

namespace ProphetSecretary.Probability

variable {ι A : Type*} [DecidableEq ι] [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]

lemma measurable_infinite_erasure (i : ι) (a0 : A) :
    Measurable (fun x : ι → A => Function.update x i a0) :=
  ProphetSecretary.Model.measurable_eraseCoordinate i a0

lemma infinite_erasure_independent (i : ι) (a0 : A) :
    IndepFun (fun x : ι → A => Function.update x i a0) (fun x => x i) (Measure.infinitePi μ) := by
  classical
  let m := fun j : ι => MeasurableSpace.comap (fun x : ι → A => x j) inferInstance
  have hFamily : iIndep m (Measure.infinitePi μ) :=
    (iIndepFun_iff_iIndep (fun _ : ι => inferInstance) (fun j (x : ι → A) => x j) _).mp
      (iIndepFun_infinitePi (P := μ) (X := fun _ => id) (fun _ => measurable_id))
  have hLe (j : ι) : m j ≤ (inferInstance : MeasurableSpace (ι → A)) := (measurable_pi_apply j).comap_le
  have hSplit : Indep (⨆ j∈({i} : Set ι)ᶜ, m j) (m i) (Measure.infinitePi μ) := by
    have h := indep_iSup_of_disjoint hLe hFamily
      (S := ({i} : Set ι)ᶜ) (T := {i}) (by simp)
    simpa only [iSup_singleton] using h
  have hErase : MeasurableSpace.comap (fun x : ι → A => Function.update x i a0) inferInstance ≤
      ⨆ j∈({i} : Set ι)ᶜ, m j := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro j
    by_cases hj : j=i
    · subst j
      have heq : (fun x : ι → A => Function.update x i a0 i) = fun _ => a0 := by funext x; simp
      rw [heq,MeasurableSpace.comap_const]
      exact bot_le
    · have heq : (fun x : ι → A => Function.update x i a0 j) = fun x => x j := by
        funext x
        simp [hj]
      rw [heq]
      exact le_iSup_of_le j (le_iSup_of_le (by simpa using hj) le_rfl)
  apply (IndepFun_iff_Indep _ _ _).mpr
  rw [Indep_iff] at hSplit ⊢
  intro S T hS hT
  exact hSplit S T (hErase S hS) hT

lemma infinite_erasedFunctional_independent {B : Type*} [MeasurableSpace B]
    (i : ι) (a0 : A) (f : (ι → A) → B) (hf : Measurable f) :
    IndepFun (fun x : ι → A => f (Function.update x i a0)) (fun x => x i) (Measure.infinitePi μ) :=
  (infinite_erasure_independent μ i a0).comp hf measurable_id

end ProphetSecretary.Probability
