import ProphetSecretary.Statistics.SelectedCandidateContribution
import ProphetSecretary.Statistics.EmpiricalFrozenCanonical
import ProphetSecretary.Model.EmpiricalConditionalValues

/-!
# Actual learner regret reduces to the sum of candidate contributions

The law-independent learner is evaluated under the true instance after training.
Every training outcome uses exactly the empirical canonical rule at its selected
scalar. Thus the general Bellman loss inequality and the justified removal of
the candidate's clock apply before the independent training average is taken.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type} [MeasurableSpace Seed]

theorem Learner.empiricalSelectedScalar_integral_regret_le_candidates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ p, Z p∈Icc (0:ℝ) hi) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw k).prod ν) ≤
      ∑ i : Fin n, ∫ p, selectedCandidateContribution P Z i p ∂(P.trainingCoordinateLaw k).prod ν := by
  let L := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
  let f : Reservoir n k × Seed → ℝ := fun p => optimalScalarValue P 1 (Z p)-
    (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  let e := (reservoirCoordinates (n:=n) (k:=k)).symm.prodCongr (MeasurableEquiv.refl Seed)
  have hP := P.integrable_maximum_of_bounded hbound
  have hmp : MeasurePreserving e ((P.trainingCoordinateLaw k).prod ν) ((P.reservoirLaw k).prod ν) :=
    (P.reservoirCoordinates_symm_measurePreserving k).prod (MeasurePreserving.id ν)
  have hf : Integrable f ((P.reservoirLaw k).prod ν) :=
    L.integrable_selectedRegret P hP hZ (fun p => (hZrange p).1)
      (Eventually.of_forall fun p => (hZrange p).2)
  have hcomp := hmp.integrable_comp_of_integrable hf
  have hC (i : Fin n) := integrable_selectedCandidateContribution P hbound hZ hZrange i ν
  change (∫ p, f p ∂(P.reservoirLaw k).prod ν) ≤ _
  rw [←hmp.integral_comp' f,←integral_finsetSum _ (fun i _ => hC i)]
  apply integral_mono_ae hcomp (integrable_finsetSum _ (fun i _ => hC i))
  exact Eventually.of_forall fun p => by
    have h := Learner.empiricalSelectedScalar_frozen_regret_bound Seed ν Z hZ
      (reservoirCoordinates.symm p.1) p.2 (hZrange _).1 P hP
    change f (e p) ≤ _
    apply h.trans_eq
    apply Finset.sum_congr rfl
    intro i _
    exact (empirical_candidateMean_integral_otherClocks P hP p.1 (hZrange _).1 i).2

end ProphetSecretary.Model
