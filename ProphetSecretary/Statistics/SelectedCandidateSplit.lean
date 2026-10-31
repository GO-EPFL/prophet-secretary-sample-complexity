import ProphetSecretary.Statistics.SelectedCandidateContribution

/-!
# Candidate-row and auxiliary-seed disintegration

This is the actual product-law identity for a scalar selected from all samples
and independent auxiliary randomness. The candidate's row is frozen along with
the seed, leaving a measurable scalar depending only on the other training rows.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type*} [MeasurableSpace Seed]

/-- The order of integration used for a data-selected scalar is licensed by
actual integrability and the measure-preserving training-row equivalence. -/
theorem integral_selectedCandidateContribution_split (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ p, Z p∈Icc (0:ℝ) hi) (i : Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ p, selectedCandidateContribution P Z i p ∂(P.trainingCoordinateLaw k).prod ν) =
      ∫ r, (∫ b, (∫ v, (∫ x, (∫ t,
        empiricalClockGapLoss (P.restrictTo (Finset.univ.erase i)) (reservoirCoordinates.symm b)
          (frozenOtherScalar Z i r b) v x t ∂Instance.uniformClock) ∂P.law i)
        ∂Instance.clocksLaw (Finset.univ.erase i).card)
        ∂(P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k)
        ∂(Measure.pi (fun _ : Fin k => P.law i)).prod ν := by
  let f := selectedCandidateContribution P Z i
  let e := splitTrainingRowSeedEquiv (k:=k) (Seed:=Seed) i
  have hf := integrable_selectedCandidateContribution P hbound hZ hZrange i ν
  have hmp := P.mergeTrainingRowSeed_measurePreserving (k:=k) i ν
  have hcomp : Integrable (fun q => f (e.symm q))
      (((P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k).prod
        ((Measure.pi (fun _ : Fin k => P.law i)).prod ν)) :=
    hmp.integrable_comp_of_integrable hf
  rw [←hmp.integral_comp' f,integral_prod_symm _ hcomp]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => integral_congr_ae (Eventually.of_forall fun b =>
    selectedCandidateContribution_merge P Z i b r)

end ProphetSecretary.Model
