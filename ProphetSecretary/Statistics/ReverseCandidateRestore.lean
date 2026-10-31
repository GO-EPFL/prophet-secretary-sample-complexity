import ProphetSecretary.Statistics.ReverseCandidateAveraging

/-!
# Full product-law restoration for fixed-scalar reverse candidate loss

The exact own-row average is integrated using the actual training-row product
law. Integrable local losses justify moving the candidate's true marginal
through the other clocks. The equality retains every identity and clock.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma reverseCandidateKernel_fubini (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (hb : ∀ j l, b (j,l)≤1) :
    (∫ x, reverseCandidateKernel P z i b x ∂P.law i) =
      ∫ v, (∫ x, (∫ t, trueClockGapLossEmpiricalEval (P.restrictTo (Finset.univ.erase i))
        (reservoirCoordinates.symm b) z v x t ∂Instance.uniformClock) ∂P.law i)
        ∂Instance.clocksLaw (Finset.univ.erase i).card := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let T := (((Fin A.card → ℝ) × ℝ) × ℝ)
  let F : T → ℝ := fun q => trueClockGapLossEmpiricalEval (P.restrictTo A)
    (reservoirCoordinates.symm b) z q.1.1 q.1.2 q.2
  have hm : Measurable F := measurable_trueClockGapLossEmpiricalEval (P.restrictTo A)
    (P.restrictTo_integrable_maximum A (P.integrable_maximum_of_bounded hbound))
    (fun _ _ => measurable_const) measurable_const measurable_snd (measurable_snd.comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)) (fun _ => hz)
  have hI : Integrable F (((Instance.clocksLaw A.card).prod (P.law i)).prod Instance.uniformClock) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (2+2*hi)
    have ht := (measurePreserving_snd (μ:=(Instance.clocksLaw A.card).prod (P.law i))
      (ν:=Instance.uniformClock)).quasiMeasurePreserving.ae uniformClock_nonnegative_ae
    filter_upwards [ht] with q ht
    change ‖trueClockGapLossEmpiricalEval _ _ _ _ _ _‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (trueClockGapLossEmpiricalEval_nonnegative _ _ _ _ _ _)]
    exact (paired_clockGapLoss_bounded (P.restrictTo A) (fun j => hbound (stateEmbedding A j))
      (reservoirCoordinates.symm b) hb hz hzhi ht q.1.1 q.1.2).2
  exact (integral_integral_swap hI.integral_prod_left).symm

/-- At a fixed scalar, averaging the empirical candidate law restores the true
candidate law inside the full training expectation. -/
theorem integral_reverseCandidateContribution_restore (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi) (i : Fin n) :
    (∫ a, reverseCandidateContribution P z i a ∂P.trainingCoordinateLaw k) =
      ∫ b, (∫ v, (∫ x, (∫ t,
        trueClockGapLossEmpiricalEval (P.restrictTo (Finset.univ.erase i)) (reservoirCoordinates.symm b) z v x t
        ∂Instance.uniformClock) ∂P.law i) ∂Instance.clocksLaw (Finset.univ.erase i).card)
        ∂(P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k := by
  let e := splitTrainingRowEquiv (k:=k) i
  let f := reverseCandidateContribution (k:=k) P z i
  have hmp := (P.splitTrainingRow_measurePreserving (k:=k) i).symm e
  have hI := integrable_reverseCandidateContribution (k:=k) P hbound hz hzhi i
  have hcomp : Integrable (fun q => f (e.symm q))
      (((P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k).prod (Measure.pi (fun _ : Fin k => P.law i))) :=
    hmp.integrable_comp_of_integrable hI
  rw [←hmp.integral_comp' f,integral_prod _ hcomp]
  apply integral_congr_ae
  filter_upwards [(P.restrictTo (Finset.univ.erase i)).trainingCoordinates_bounded (k:=k)
    (fun j => hbound (stateEmbedding (Finset.univ.erase i) j))] with b hb
  exact (integral_reverseCandidateContribution_ownRow P hbound hz hzhi i b hb).trans
    (reverseCandidateKernel_fubini P hbound hz hzhi i b hb)

end ProphetSecretary.Model
