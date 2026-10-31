import ProphetSecretary.Statistics.EmpiricalCandidateReverseMean
import ProphetSecretary.Statistics.DataSelectedClockLossIntegrability

/-!
# Empirical-evaluation candidate contributions at a fixed scalar

A reverse contribution is the average over the candidate's own sample row of
its potential empirical loss. The continuation uses only other rows. Its joint
measurability and integrability are established before restoring the candidate's
true marginal by averaging that row.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def reverseCandidateContribution (P : Instance n) (z : ℝ) (i : Fin n)
    (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (k:ℝ)⁻¹ * ∑ l : Fin k, ∫ v, (∫ t,
    trueClockGapLossEmpiricalEval (P.restrictTo (Finset.univ.erase i))
      (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a))
      z v (max 0 (a (i,l))) t ∂Instance.uniformClock) ∂Instance.clocksLaw (Finset.univ.erase i).card

lemma measurable_reverseCandidateContribution (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0≤z) (i : Fin n) :
    Measurable (reverseCandidateContribution (k:=k) P z i) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro l _
  let A := (Finset.univ : Finset (Fin n)).erase i
  let T := ((((Fin n × Fin k) → ℝ) × (Fin A.card → ℝ)) × ℝ)
  have hm : Measurable (fun q : T => trueClockGapLossEmpiricalEval (P.restrictTo A)
      (reservoirCoordinates.symm (restrictTrainingCoordinates A q.1.1)) z q.1.2 (max 0 (q.1.1 (i,l))) q.2) :=
    measurable_trueClockGapLossEmpiricalEval (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
      (fun j s => (measurable_pi_apply (stateEmbedding A j,s)).comp (measurable_fst.comp measurable_fst))
      measurable_const measurable_snd (measurable_const.max ((measurable_pi_apply (i,l)).comp (measurable_fst.comp measurable_fst)))
      (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)) (fun _ => hz)
  exact (hm.stronglyMeasurable.integral_prod_right'.integral_prod_right').measurable

lemma reverseCandidateContribution_nonnegative (P : Instance n) (z : ℝ) (i : Fin n)
    (a : (Fin n × Fin k) → ℝ) : 0≤reverseCandidateContribution P z i a := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))
  exact Finset.sum_nonneg fun l _ => integral_nonneg fun v => integral_nonneg fun t =>
    trueClockGapLossEmpiricalEval_nonnegative _ _ _ _ _ _

lemma reverseCandidateContribution_norm_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi)
    (i : Fin n) (a : (Fin n × Fin k) → ℝ) (ha : ∀ j l, a (j,l)≤1) :
    ‖reverseCandidateContribution P z i a‖≤2+2*hi := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let Q := P.restrictTo A
  let y := reservoirCoordinates.symm (restrictTrainingCoordinates A a)
  have hQ : ∀ j, ∀ᵐ x ∂Q.law j, x≤1 := fun j => hbound (stateEmbedding A j)
  have hy : ∀ j l, y j l≤1 := fun j l => ha (stateEmbedding A j) l
  have hT (v : Fin A.card → ℝ) (x : ℝ) :
      ‖∫ t, trueClockGapLossEmpiricalEval Q y z v x t ∂Instance.uniformClock‖≤2+2*hi := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=Instance.uniformClock)
      (f:=fun t => trueClockGapLossEmpiricalEval Q y z v x t) (C:=2+2*hi) (by
        filter_upwards [uniformClock_nonnegative_ae] with t ht
        rw [Real.norm_eq_abs,abs_of_nonneg (trueClockGapLossEmpiricalEval_nonnegative _ _ _ _ _ _)]
        exact (paired_clockGapLoss_bounded Q hQ y hy hz hzhi ht v x).2)
  have hV (x : ℝ) :
      ‖∫ v, (∫ t, trueClockGapLossEmpiricalEval Q y z v x t ∂Instance.uniformClock) ∂Instance.clocksLaw A.card‖≤2+2*hi := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=Instance.clocksLaw A.card) (Eventually.of_forall fun v => hT v x)
  have hk : (0:ℝ)<k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  unfold reverseCandidateContribution
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hk.le)]
  calc
    _ ≤ (k:ℝ)⁻¹ * ∑ l : Fin k, ‖∫ v, (∫ t,
        trueClockGapLossEmpiricalEval Q y z v (max 0 (a (i,l))) t ∂Instance.uniformClock) ∂Instance.clocksLaw A.card‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hk.le)
    _ ≤ (k:ℝ)⁻¹ * ∑ _l : Fin k, (2+2*hi) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hV _) (inv_nonneg.mpr hk.le)
    _ = _ := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]; field_simp

lemma integrable_reverseCandidateContribution (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi) (i : Fin n) :
    Integrable (reverseCandidateContribution (k:=k) P z i) (P.trainingCoordinateLaw k) := by
  apply Integrable.of_bound (measurable_reverseCandidateContribution P
    (P.integrable_maximum_of_bounded hbound) hz i).aestronglyMeasurable (2+2*hi)
  exact (P.trainingCoordinates_bounded (k:=k) hbound).mono fun a ha =>
    reverseCandidateContribution_norm_le P hbound hz hzhi i a ha

end ProphetSecretary.Model
