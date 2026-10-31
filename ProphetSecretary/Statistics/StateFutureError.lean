import ProphetSecretary.Statistics.RestartKernelMoments
import ProphetSecretary.Probability.TrainingClockRestartConditioning

/-!
# A measurable error variable evaluated at the actual unseen state

The finite-state sum is a measurable representation: exactly one summand is
active. The training restriction and normalized clocks are actual observed-state
coordinates. Refreshing the pending clocks gives the already proved restart
kernel on every fixed prefix, while all training is averaged independently.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma measurable_pendingClockSet (t : ℝ) : Measurable (pendingClockSet (n := n) t) := by
  rw [measurable_finset_iff]
  intro i
  apply measurableSet_setOf.mp
  simpa only [Set.preimage_setOf_eq, mem_pendingClockSet] using
    (measurableSet_le measurable_const (measurable_pi_apply i))

lemma pendingClockSet_refresh {t : ℝ} (ht : t ≤ 1) (u v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    pendingClockSet t (refreshClocks t (u,v)) = pendingClockSet t u := by
  apply Finset.ext
  intro i
  rw [mem_pendingClockSet, mem_pendingClockSet]
  by_cases hi : u i < t
  · simp only [refreshClocks, refreshClock, if_pos hi, not_le.mpr hi]
  · have hpos : 0 ≤ (1-t)*v i := mul_nonneg (sub_nonneg.mpr ht) (hv i)
    simp only [refreshClocks, refreshClock, if_neg hi, Model.Instance.tailClock]
    exact ⟨fun _ => le_of_not_gt hi, fun _ => by linarith only [hpos]⟩

end ProphetSecretary.Probability

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def stateTrainingFutureCoordinates (A : Finset (Fin n)) (t : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    (((Fin A.card × Fin k) → ℝ) × (Fin A.card → ℝ)) :=
  (restrictTrainingCoordinates A q.1, fun j => (q.2 (stateEmbedding A j)-t)/(1-t))

omit [NeZero k] in
lemma measurable_stateTrainingFutureCoordinates (A : Finset (Fin n)) (t : ℝ) :
    Measurable (stateTrainingFutureCoordinates (k := k) A t) :=
  ((measurable_restrictTrainingCoordinates A).comp measurable_fst).prodMk
    (measurable_pi_lambda _ (fun j => by fun_prop))

noncomputable def Instance.stateFutureError (P : Instance n) (k : ℕ) [NeZero k]
    (lo hi t : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ A : Finset (Fin n), if ProphetSecretary.Probability.pendingClockSet t q.2 = A then
    (P.restrictTo A).empiricalFutureError k (lo*(1-t)) (hi*(1-t)) (stateTrainingFutureCoordinates A t q) else 0

lemma Instance.stateFutureError_eq (P : Instance n) (lo hi t : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    P.stateFutureError k lo hi t q =
      (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).empiricalFutureError k
        (lo*(1-t)) (hi*(1-t))
        (stateTrainingFutureCoordinates (ProphetSecretary.Probability.pendingClockSet t q.2) t q) := by
  unfold stateFutureError
  rw [Finset.sum_eq_single (ProphetSecretary.Probability.pendingClockSet t q.2)]
  · exact if_pos rfl
  · intro A _ hA
    exact if_neg (Ne.symm hA)
  · simp

lemma Instance.measurable_stateFutureError (P : Instance n) (lo hi t : ℝ) :
    Measurable (P.stateFutureError k lo hi t) := by
  apply Finset.measurable_sum
  intro A _
  apply Measurable.ite
    (measurableSet_eq_fun ((ProphetSecretary.Probability.measurable_pendingClockSet t).comp measurable_snd) measurable_const)
  · exact ((P.restrictTo A).measurable_empiricalFutureError _ _).comp (measurable_stateTrainingFutureCoordinates A t)
  · exact measurable_const

lemma Instance.stateFutureError_nonnegative (P : Instance n) (lo hi t : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : 0 ≤ P.stateFutureError k lo hi t q := by
  rw [P.stateFutureError_eq]
  exact (P.restrictTo _).empiricalCountableFutureError_nonnegative _ _ _ _

/-- The reset is an identity of actual functions, rather than an independence
assumption imposed on a random entrance state. -/
lemma Instance.stateFutureError_restart (P : Instance n) (lo hi : ℝ) {t : ℝ} (ht : t < 1)
    (q r : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (hr : ∀ i, 0 ≤ r.2 i) :
    P.stateFutureError k lo hi t (ProphetSecretary.Probability.restartTrainingClocks t (q,r)) =
      P.restartedFutureError k lo hi t q.2 r := by
  rw [P.stateFutureError_eq]
  have hA := ProphetSecretary.Probability.pendingClockSet_refresh ht.le q.2 r.2 hr
  have hA' : ProphetSecretary.Probability.pendingClockSet t
      (ProphetSecretary.Probability.restartTrainingClocks t (q,r)).2 =
      ProphetSecretary.Probability.pendingClockSet t q.2 := hA
  have he := congrArg (fun A => (P.restrictTo A).empiricalFutureError k (lo*(1-t)) (hi*(1-t))
    (stateTrainingFutureCoordinates A t (ProphetSecretary.Probability.restartTrainingClocks t (q,r)))) hA'
  exact he.trans rfl

end ProphetSecretary.Model
