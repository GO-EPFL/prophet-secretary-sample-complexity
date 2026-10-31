import ProphetSecretary.Statistics.MixedRestartKernelMoments
import ProphetSecretary.Statistics.StateFutureError

/-!
# Actual mixed error at a measurable unseen state

The finite-state sum activates exactly the actual unseen identity set, with its
known labels pulled back through the same embedding. Training restriction and
clock normalization are constructed coordinates. Refreshing clocks yields the
proved mixed restart kernel on every fixed prefix.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def Instance.mixedStateFutureError (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k]
    (lo hi t : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ A : Finset (Fin n), if ProphetSecretary.Probability.pendingClockSet t q.2 = A then
    (P.restrictTo A).mixedFutureError (knownInState known A) k (lo*(1-t)) (hi*(1-t)) (stateTrainingFutureCoordinates A t q) else 0

lemma Instance.mixedStateFutureError_eq (P : Instance n) (known : Finset (Fin n)) (lo hi t : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    P.mixedStateFutureError known k lo hi t q =
      (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).mixedFutureError
      (knownInState known (ProphetSecretary.Probability.pendingClockSet t q.2)) k
        (lo*(1-t)) (hi*(1-t))
        (stateTrainingFutureCoordinates (ProphetSecretary.Probability.pendingClockSet t q.2) t q) := by
  unfold mixedStateFutureError
  rw [Finset.sum_eq_single (ProphetSecretary.Probability.pendingClockSet t q.2)]
  · exact if_pos rfl
  · intro A _ hA
    exact if_neg (Ne.symm hA)
  · simp

lemma Instance.measurable_mixedStateFutureError (P : Instance n) (known : Finset (Fin n)) (lo hi t : ℝ) :
    Measurable (P.mixedStateFutureError known k lo hi t) := by
  apply Finset.measurable_sum
  intro A _
  apply Measurable.ite
    (measurableSet_eq_fun ((ProphetSecretary.Probability.measurable_pendingClockSet t).comp measurable_snd) measurable_const)
  · exact ((P.restrictTo A).measurable_mixedFutureError (knownInState known A) _ _).comp (measurable_stateTrainingFutureCoordinates A t)
  · exact measurable_const

lemma Instance.mixedStateFutureError_nonnegative (P : Instance n) (known : Finset (Fin n)) (lo hi t : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : 0 ≤ P.mixedStateFutureError known k lo hi t q := by
  rw [P.mixedStateFutureError_eq]
  exact (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).mixedCountableFutureError_nonnegative
    (knownInState known (ProphetSecretary.Probability.pendingClockSet t q.2)) _ _ _ _

/-- The reset is an identity of actual functions, rather than an independence
assumption imposed on a random entrance state. -/
lemma Instance.mixedStateFutureError_restart (P : Instance n) (known : Finset (Fin n)) (lo hi : ℝ) {t : ℝ} (ht : t < 1)
    (q r : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (hr : ∀ i, 0 ≤ r.2 i) :
    P.mixedStateFutureError known k lo hi t (ProphetSecretary.Probability.restartTrainingClocks t (q,r)) =
      P.mixedRestartedFutureError known k lo hi t q.2 r := by
  rw [P.mixedStateFutureError_eq]
  have hA := ProphetSecretary.Probability.pendingClockSet_refresh ht.le q.2 r.2 hr
  have hA' : ProphetSecretary.Probability.pendingClockSet t
      (ProphetSecretary.Probability.restartTrainingClocks t (q,r)).2 =
      ProphetSecretary.Probability.pendingClockSet t q.2 := hA
  have he := congrArg (fun A => (P.restrictTo A).mixedFutureError (knownInState known A) k (lo*(1-t)) (hi*(1-t))
    (stateTrainingFutureCoordinates A t (ProphetSecretary.Probability.restartTrainingClocks t (q,r)))) hA'
  exact he.trans rfl

end ProphetSecretary.Model
