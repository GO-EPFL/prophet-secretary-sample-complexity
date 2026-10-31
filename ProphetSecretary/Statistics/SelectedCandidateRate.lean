import ProphetSecretary.Statistics.SelectedCandidateSplit
import ProphetSecretary.Statistics.CandidateRateIntegration
import ProphetSecretary.Statistics.DataSelectedCandidateRate
import ProphetSecretary.Model.TruncatedReward

/-!
# Candidate regret rate with all training data and independent randomness

The own sample row and auxiliary seed are genuinely split from the other rows.
After they are fixed, the uniform-in-scalar clock estimate applies to the
resulting measurable selector. The candidate's independent true value is then
integrated against its original marginal, and the frozen inputs are averaged.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type*} [MeasurableSpace Seed]

theorem integral_selectedCandidateContribution_rate (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi)
    (i : Fin n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ p, selectedCandidateContribution P Z i p ∂(P.trainingCoordinateLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi * (1+(P.restrictTo (Finset.univ.erase i)).totalFirstMoment)*
        (∫ x, x ∂P.law i)/(k:ℝ) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let Q := P.restrictTo A
  let B := empiricalCandidateRegretConstant lo hi*(1+Q.totalFirstMoment)/(k:ℝ)
  let f := selectedCandidateContribution P Z i
  let e := splitTrainingRowSeedEquiv (k:=k) (Seed:=Seed) i
  have hZ0 : ∀ p, Z p∈Icc (0:ℝ) hi := fun p => ⟨(hlo.trans_le (hZrange p).1).le,(hZrange p).2⟩
  have hf := integrable_selectedCandidateContribution P hbound hZ hZ0 i ν
  have hmp := P.mergeTrainingRowSeed_measurePreserving (k:=k) i ν
  have hcomp : Integrable (fun q => f (e.symm q))
      ((Q.trainingCoordinateLaw k).prod ((Measure.pi (fun _ : Fin k => P.law i)).prod ν)) :=
    hmp.integrable_comp_of_integrable hf
  have hQ : ∀ j, ∀ᵐ x ∂Q.law j, x≤1 := fun j => hbound (stateEmbedding A j)
  have hP := P.integrable_maximum_of_bounded hbound
  have hr (r : (Fin k → ℝ) × Seed) :
      (∫ b, f (e.symm (b,r)) ∂Q.trainingCoordinateLaw k) ≤ B*(∫ x, x ∂P.law i) := by
    let Zr := frozenOtherScalar Z i r
    have hm : Measurable Zr := measurable_frozenOtherScalar hZ i r
    have hz : ∀ b, Zr b∈Icc lo hi := frozenOtherScalar_range hZrange i r
    have hrate (x : ℝ) (hx : 0≤x) :
        (∫ q, ∫ t, dataSelectedClockLoss Q Zr x q t ∂Instance.uniformClock
          ∂(Q.trainingCoordinateLaw k).prod (Instance.clocksLaw A.card))≤B*x ∧
        (∫ q, ∫ t, dataSelectedClockLossReverse Q Zr x q t ∂Instance.uniformClock
          ∂(Q.trainingCoordinateLaw k).prod (Instance.clocksLaw A.card))≤B*x := by
      constructor
      · simpa [B,div_mul_eq_mul_div,dataSelectedClockLossDirection] using Q.dataSelectedClockLossDirection_rate hQ hm hlo hlohi hz hx false
      · simpa [B,div_mul_eq_mul_div,dataSelectedClockLossDirection] using Q.dataSelectedClockLossDirection_rate hQ hm hlo hlohi hz hx true
    have h := (Q.integrated_candidateRate hQ hm
      (fun b => ⟨(hlo.trans_le (hz b).1).le,(hz b).2⟩) (P.law i) (P.nonnegative i)
      (P.integrable_maximum_iff.mp hP i) hrate).1
    apply le_trans ?_ h
    apply le_of_eq
    apply integral_congr_ae
    exact Eventually.of_forall fun b => selectedCandidateContribution_merge P Z i b r
  change (∫ p, f p ∂(P.trainingCoordinateLaw k).prod ν)≤_
  rw [←hmp.integral_comp' f,integral_prod_symm _ hcomp]
  calc
    _ ≤ ∫ _r, B*(∫ x, x ∂P.law i) ∂(Measure.pi (fun _ : Fin k => P.law i)).prod ν :=
      integral_mono_ae hcomp.integral_prod_right (integrable_const _) (Eventually.of_forall hr)
    _ = _ := by simp [B]; ring

/-- A common full-instance coefficient is used before summing candidates. -/
theorem integral_selectedCandidateContribution_rate_full (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi)
    (i : Fin n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ p, selectedCandidateContribution P Z i p ∂(P.trainingCoordinateLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi * (1+P.totalFirstMoment)*(∫ x, x ∂P.law i)/(k:ℝ) := by
  apply (integral_selectedCandidateContribution_rate P hbound hZ hlo hlohi hZrange i ν).trans
  have hm : 0≤∫ x, x ∂P.law i := integral_nonneg_of_ae (P.nonnegative i)
  have hK := (empiricalCandidateRegretConstant_positive hlo hlohi).le
  have hS := P.totalFirstMoment_restrictTo_le (Finset.univ.erase i)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hS) hK) hm

end ProphetSecretary.Model
