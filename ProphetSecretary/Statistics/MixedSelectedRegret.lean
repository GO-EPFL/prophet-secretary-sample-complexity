import ProphetSecretary.Statistics.MixedFrozenCanonical
import ProphetSecretary.Statistics.MixedCandidateClockMean
import ProphetSecretary.Statistics.MixedSelectedCandidateRate
import ProphetSecretary.Statistics.CanonicalRegretCandidateBound
import ProphetSecretary.Model.EmpiricalConditionalValues

/-!
# Actual selected-scalar learner regret with known marginals

The implemented causal learner is exactly canonical on every frozen history.
Its true-online performance difference reduces to the proved TRUE-candidate
contributions, whose actual full-training/auxiliary average has the original
inverse-linear constant. Budgets remain outcome-wise statements of the learner.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k] {Seed : Type} [MeasurableSpace Seed]

theorem Learner.mixedSelectedScalar_integral_regret_le_candidates (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ p, Z p∈Icc (0:ℝ) hi) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.mixedEmpiricalWithSelectedWeights P (P.integrable_maximum_of_bounded hbound) known
        Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw k).prod ν) ≤
      ∑ i : Fin n, ∫ p, mixedSelectedCandidateContribution P known Z false i p ∂(P.trainingCoordinateLaw k).prod ν := by
  have hP := P.integrable_maximum_of_bounded hbound
  let L := Learner.mixedEmpiricalWithSelectedWeights P hP known Seed ν (fun _ => 1) Z measurable_const hZ
  let f : Reservoir n k × Seed → ℝ := fun p => optimalScalarValue P 1 (Z p)-
    (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  let e := (reservoirCoordinates (n:=n) (k:=k)).symm.prodCongr (MeasurableEquiv.refl Seed)
  have hmp : MeasurePreserving e ((P.trainingCoordinateLaw k).prod ν) ((P.reservoirLaw k).prod ν) :=
    (P.reservoirCoordinates_symm_measurePreserving k).prod (MeasurePreserving.id ν)
  have hf : Integrable f ((P.reservoirLaw k).prod ν) :=
    L.integrable_selectedRegret P hP hZ (fun p => (hZrange p).1)
      (Eventually.of_forall fun p => (hZrange p).2)
  have hcomp := hmp.integrable_comp_of_integrable hf
  have hC (i : Fin n) := integrable_mixedSelectedCandidateContribution P known hbound hZ hZrange false i ν
  change (∫ p, f p ∂(P.reservoirLaw k).prod ν) ≤ _
  rw [←hmp.integral_comp' f,←integral_finsetSum _ (fun i _ => hC i)]
  apply integral_mono_ae hcomp (integrable_finsetSum _ (fun i _ => hC i))
  exact Eventually.of_forall fun p => by
    have hz : 0≤Z (reservoirCoordinates.symm p.1,p.2) := (hZrange _).1
    have hObj := Learner.mixedEmpiricalWithSelectedWeights_frozen_objective_eq P hP known Seed ν
      (fun _ => 1) Z measurable_const hZ (reservoirCoordinates.symm p.1) p.2 zero_lt_one hz P 1
      (Z (reservoirCoordinates.symm p.1,p.2))
    change optimalScalarValue P 1 (Z (reservoirCoordinates.symm p.1,p.2))-
      (L.frozenRandomizedPolicy (reservoirCoordinates.symm p.1) p.2).scalarObjective P 1
        (Z (reservoirCoordinates.symm p.1,p.2))≤_
    rw [hObj]
    apply ((mixedEmpiricalInstance P known (reservoirCoordinates.symm p.1)).canonical_regret_le_sum_candidateLossMean
      P (mixedEmpiricalInstance_integrable P hP known _) hP hz).trans_eq
    exact Finset.sum_congr rfl fun i _ => (mixed_fullCandidateMean_integral_otherClocks P hP known p.1 hz false i).2

/-- The selected-weight part of the exact-known-marginal extension, with an
explicit constant chosen before the instance and its declared known set. -/
theorem Learner.mixedSelectedScalar_expected_regret_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.mixedEmpiricalWithSelectedWeights P (P.integrable_maximum_of_bounded hbound) known
        Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) :=
  (Learner.mixedSelectedScalar_integral_regret_le_candidates P known hbound ν hZ
    (fun p => ⟨(hlo.trans_le (hZrange p).1).le,(hZrange p).2⟩)).trans
      (sum_integral_mixedSelectedCandidateContribution_rate P known hbound hZ hlo hlohi hZrange false ν)

end ProphetSecretary.Model
