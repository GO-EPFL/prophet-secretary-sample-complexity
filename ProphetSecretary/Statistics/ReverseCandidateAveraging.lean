import ProphetSecretary.Statistics.ReverseCandidateContribution
import ProphetSecretary.Statistics.TrainingScalarFreeze
import ProphetSecretary.Statistics.EmpiricalResidual

/-!
# Restoring the true candidate marginal at a fixed scalar

After the other sample rows are fixed, the empirical candidate evaluation is
a literal average of one fixed measurable loss function over the own row.
Independent sample averaging restores the true marginal. No such centering is
asserted for a scalar selected using that row.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def reverseCandidateKernel (P : Instance n) (z : ℝ) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (x : ℝ) : ℝ :=
  ∫ v, (∫ t, trueClockGapLossEmpiricalEval (P.restrictTo (Finset.univ.erase i))
    (reservoirCoordinates.symm b) z v x t ∂Instance.uniformClock)
    ∂Instance.clocksLaw (Finset.univ.erase i).card

lemma measurable_reverseCandidateKernel (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0≤z) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) : Measurable (reverseCandidateKernel P z i b) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  have hm : Measurable (fun q : (ℝ × (Fin A.card → ℝ)) × ℝ =>
      trueClockGapLossEmpiricalEval (P.restrictTo A) (reservoirCoordinates.symm b) z q.1.2 q.1.1 q.2) :=
    measurable_trueClockGapLossEmpiricalEval (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
      (fun _ _ => measurable_const) measurable_const measurable_snd (measurable_fst.comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)) (fun _ => hz)
  exact (hm.stronglyMeasurable.integral_prod_right'.integral_prod_right').measurable

lemma reverseCandidateKernel_norm_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (hb : ∀ j l, b (j,l)≤1) (x : ℝ) :
    ‖reverseCandidateKernel P z i b x‖≤2+2*hi := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  have hV (v : Fin A.card → ℝ) :
      ‖∫ t, trueClockGapLossEmpiricalEval (P.restrictTo A) (reservoirCoordinates.symm b) z v x t
        ∂Instance.uniformClock‖≤2+2*hi := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=Instance.uniformClock)
      (f:=fun t => trueClockGapLossEmpiricalEval (P.restrictTo A) (reservoirCoordinates.symm b) z v x t)
      (C:=2+2*hi) (by
        filter_upwards [uniformClock_nonnegative_ae] with t ht
        rw [Real.norm_eq_abs,abs_of_nonneg (trueClockGapLossEmpiricalEval_nonnegative _ _ _ _ _ _)]
        exact (paired_clockGapLoss_bounded (P.restrictTo A) (fun j => hbound (stateEmbedding A j))
          (reservoirCoordinates.symm b) hb hz hzhi ht v x).2)
  simpa only [reverseCandidateKernel,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=Instance.clocksLaw A.card) (Eventually.of_forall hV)

omit [NeZero k] in
lemma ownTrainingCoordinate_merge (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (r : Fin k → ℝ) (l : Fin k) :
    ((splitTrainingRowEquiv i).symm (b,r)) (i,l) = r l := by
  have he := (splitTrainingRowEquiv (k:=k) i).apply_symm_apply (b,r)
  have hs := congrArg Prod.snd he
  exact congrFun hs l

lemma reverseCandidateContribution_merge (P : Instance n) (z : ℝ) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (r : Fin k → ℝ) :
    reverseCandidateContribution P z i ((splitTrainingRowEquiv i).symm (b,r)) =
      (k:ℝ)⁻¹ * ∑ l : Fin k, reverseCandidateKernel P z i b (max 0 (r l)) := by
  unfold reverseCandidateContribution reverseCandidateKernel
  rw [restrictTrainingCoordinates_merge]
  simp_rw [ownTrainingCoordinate_merge]

/-- Conditional on all other rows, the complete empirical own-row average has
exactly the true candidate expectation, because z was fixed before training. -/
theorem integral_reverseCandidateContribution_ownRow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (hb : ∀ j l, b (j,l)≤1) :
    (∫ r, reverseCandidateContribution P z i ((splitTrainingRowEquiv i).symm (b,r))
      ∂Measure.pi (fun _ : Fin k => P.law i)) = ∫ x, reverseCandidateKernel P z i b x ∂P.law i := by
  let f := reverseCandidateKernel P z i b
  have hm := measurable_reverseCandidateKernel P (P.integrable_maximum_of_bounded hbound) hz i b
  have hI : Integrable f (P.law i) := Integrable.of_bound hm.aestronglyMeasurable (2+2*hi)
    (Eventually.of_forall (reverseCandidateKernel_norm_le P hbound hz hzhi i b hb))
  have he : (fun x : ℝ => f (max 0 x)) =ᵐ[P.law i] f := (P.nonnegative i).mono fun x hx => by
    change f (max 0 x) = f x
    rw [max_eq_right hx]
  simp_rw [reverseCandidateContribution_merge]
  have havg := ProphetSecretary.Statistics.integral_empirical_average (k:=k) (f:=fun x => f (max 0 x)) (P.law i)
    (hm.comp (measurable_const.max measurable_id)) (hI.congr he.symm)
  exact havg.trans (integral_congr_ae he)

end ProphetSecretary.Model
