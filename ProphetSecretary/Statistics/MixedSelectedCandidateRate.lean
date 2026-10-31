import ProphetSecretary.Statistics.MixedSelectedCandidateContribution
import ProphetSecretary.Statistics.MixedCandidateRateIntegration
import ProphetSecretary.Model.TruncatedReward

/-!
# Mixed candidate rates after full training and auxiliary averaging

The candidate's complete sample row and independent auxiliary seed are genuinely
split from the other rows. Holding them fixed leaves a measurable other-row
scalar selector. Both directions then integrate the true candidate marginal
with the original explicit constant, before the frozen inputs are averaged.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k] {Seed : Type*} [MeasurableSpace Seed]

theorem integral_mixedSelectedCandidateContribution_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi)
    (reverse : Bool) (i : Fin n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ p, mixedSelectedCandidateContribution P known Z reverse i p ∂(P.trainingCoordinateLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi*(1+(P.restrictTo (Finset.univ.erase i)).totalFirstMoment)*
        (∫ x, x ∂P.law i)/(k:ℝ) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let Q := P.restrictTo A
  let B := empiricalCandidateRegretConstant lo hi*(1+Q.totalFirstMoment)/(k:ℝ)
  let f := mixedSelectedCandidateContribution P known Z reverse i
  let e := splitTrainingRowSeedEquiv (k:=k) (Seed:=Seed) i
  have hZ0 : ∀ p, Z p∈Icc (0:ℝ) hi := fun p => ⟨(hlo.trans_le (hZrange p).1).le,(hZrange p).2⟩
  have hf := integrable_mixedSelectedCandidateContribution P known hbound hZ hZ0 reverse i ν
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
    have h := Q.integrated_mixedCandidateDirection_rate (knownInState known A) hQ hm hlo hlohi hz
      (P.law i) (P.nonnegative i) (P.integrable_maximum_iff.mp hP i) reverse
    apply le_trans ?_ (h.trans_eq (by dsimp [B]; ring))
    apply le_of_eq
    apply integral_congr_ae
    exact Eventually.of_forall fun b => mixedSelectedCandidateContribution_merge P known Z reverse i b r
  change (∫ p, f p ∂(P.trainingCoordinateLaw k).prod ν)≤_
  rw [←hmp.integral_comp' f,integral_prod_symm _ hcomp]
  calc
    _ ≤ ∫ _r, B*(∫ x, x ∂P.law i) ∂(Measure.pi (fun _ : Fin k => P.law i)).prod ν :=
      integral_mono_ae hcomp.integral_prod_right (integrable_const _) (Eventually.of_forall hr)
    _ = _ := by simp [B]; ring

theorem integral_mixedSelectedCandidateContribution_rate_full (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi)
    (reverse : Bool) (i : Fin n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ p, mixedSelectedCandidateContribution P known Z reverse i p ∂(P.trainingCoordinateLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)*(∫ x, x ∂P.law i)/(k:ℝ) := by
  apply (integral_mixedSelectedCandidateContribution_rate P known hbound hZ hlo hlohi hZrange reverse i ν).trans
  have hm : 0≤∫ x, x ∂P.law i := integral_nonneg_of_ae (P.nonnegative i)
  have hK := (empiricalCandidateRegretConstant_positive hlo hlohi).le
  have hS := P.totalFirstMoment_restrictTo_le (Finset.univ.erase i)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hS) hK) hm

theorem sum_integral_mixedSelectedCandidateContribution_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ p, Z p∈Icc lo hi)
    (reverse : Bool) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∑ i : Fin n, ∫ p, mixedSelectedCandidateContribution P known Z reverse i p ∂(P.trainingCoordinateLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  calc
    _ ≤ ∑ i : Fin n, empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)*
        (∫ x, x ∂P.law i)/(k:ℝ) := Finset.sum_le_sum fun i _ =>
      integral_mixedSelectedCandidateContribution_rate_full P known hbound hZ hlo hlohi hZrange reverse i ν
    _ = ∑ i : Fin n, (empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)/(k:ℝ))*(∫ x, x ∂P.law i) :=
      Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [←Finset.mul_sum]; unfold Instance.totalFirstMoment; ring

end ProphetSecretary.Model
