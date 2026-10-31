import ProphetSecretary.Limiting.CountableRemainingState
import ProphetSecretary.Limiting.HybridHorizon
import ProphetSecretary.Limiting.ExcessPoissonization

/-!
# Finite-mask projections of actual remaining-state truncations

Only the first N mask coordinates affect the finite prefix. Their product
space is finite and discrete. The anonymous intensity scales by the actual
remaining horizon and commutes with restricting marks above the cutoff.
-/

open MeasureTheory Set
open scoped Topology Classical NNReal

namespace ProphetSecretary.Limiting

def restrictIndividualMask (N : ℕ) (keep : IndividualMask) : Fin N → Bool := fun i => keep i.val

def extendIndividualMask {N : ℕ} (keep : Fin N → Bool) : IndividualMask :=
  fun j => if hj : j < N then keep ⟨j,hj⟩ else false

lemma continuous_restrictIndividualMask (N : ℕ) : Continuous (restrictIndividualMask N) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.val

@[simp] lemma extendIndividualMask_at_prefix {N : ℕ} (keep : Fin N → Bool) (i : Fin N) :
    extendIndividualMask keep i.val = keep i := dif_pos i.isLt

noncomputable def CountableInstance.finiteMaskState (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (keep : Fin N → Bool) : FiniteIntensityHybridInstance N :=
  (B.maskIndividuals (extendIndividualMask keep)).truncation N b hb

lemma CountableInstance.remainingState_truncation_eq (B : CountableInstance) (keep : IndividualMask)
    (u : ℝ≥0) (N : ℕ) (b : ℝ) (hb : (B.terminal : ℝ) < b) :
    (B.remainingState keep u).truncation N b hb =
      (B.finiteMaskState N b hb (restrictIndividualMask N keep)).remainingHorizon u := by
  apply FiniteIntensityHybridInstance.ext_data
  · rfl
  · rfl
  · apply Model.Instance.eq_of_law_eq
    funext i
    change (maskedProbabilityLaw (B.individuals i.val) (keep i.val) : Measure ℝ) =
      (maskedProbabilityLaw (B.individuals i.val) (extendIndividualMask (restrictIndividualMask N keep) i.val) : Measure ℝ)
    rw [extendIndividualMask_at_prefix]
    rfl
  · apply FiniteMeasure.toMeasure_injective
    change (u • B.intensity).restrict (Ioi b) = u • B.intensity.restrict (Ioi b)
    exact Measure.restrict_smul u B.intensity (Ioi b)

end ProphetSecretary.Limiting
