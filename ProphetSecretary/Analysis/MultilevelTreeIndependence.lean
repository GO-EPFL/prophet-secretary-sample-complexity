import ProphetSecretary.Analysis.MultilevelEstimatorMoments
import Mathlib.Probability.Independence.Basic

/-!
# Independent coordinates of a multilevel tree

Flattening the two finite sample-array indices preserves the product law.
This makes disjoint groups of transition and subtree coordinates available
for the independence of different multilevel summands.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Analysis

theorem measurePreserving_finitePiCurry {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] {X : (i : ι) → κ i → Type*}
    [∀ i j, MeasurableSpace (X i j)] (μ : (i : ι) → (j : κ i) → Measure (X i j))
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi (fun q : Sigma κ => μ q.1 q.2))
      (Measure.pi (fun i => Measure.pi (μ i))) := by
  let e := MeasurableEquiv.piCurry X
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, (Measure.pi_eq (fun s hs => ?_)).symm⟩
  have hpre : e.symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
    ext z
    simp [e, Set.mem_pi, Sigma.forall, Sigma.uncurry]
  rw [e.symm.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma (fun q : Sigma κ => μ q.1 q.2 (s q))).symm

/-- Measurable functions of disjoint finite coordinate groups are independent
under the actual finite product law. -/
theorem indepFun_finiteCoordinateGroups {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset ι) (hST : Disjoint S T)
    (f : ((i : S) → X i) → ℝ) (g : ((i : T) → X i) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    ProbabilityTheory.IndepFun
      (fun q : (i : ι) → X i => f (fun i : S => q i))
      (fun q : (i : ι) → X i => g (fun i : T => q i)) (Measure.pi μ) := by
  have hcoord : ProbabilityTheory.iIndepFun (fun i (q : (i : ι) → X i) => q i)
      (Measure.pi μ) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hgroups := hcoord.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  exact hgroups.comp hf hg

end ProphetSecretary.Analysis
