import ProphetSecretary.Statistics.StateFutureError
import ProphetSecretary.Model.MixedEmpiricalValueMeasurability

/-!
# Measurable actual pending values for mixed design laws

A finite-state sum retains the actual unseen identity set and its known labels.
The exact mixed restriction identity and Bellman-derived joint measurability
therefore apply to the dynamic state, without a measurable-optimizer assumption.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma measurable_mixedPendingValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (t z : ℝ) (hz : 0 ≤ z) :
    Measurable (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
        (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z) := by
  let c : ℝ := z * max 0 (1-t)
  let F : Finset (Fin n) → ((Fin n × Fin k) → ℝ) → ℝ := fun A a =>
    optimalScalarValue (mixedEmpiricalInstance (P.restrictTo A) (knownInState known A) (fun j l => a (stateEmbedding A j,l))) 1 c
  have hc0 : 0 ≤ c := mul_nonneg hz (le_max_left _ _)
  have hF (A : Finset (Fin n)) : Measurable (F A) :=
    measurable_optimalScalarValue_mixedEmpirical
      (n := A.card) (k := k) (Ω := (Fin n × Fin k) → ℝ)
      (P.restrictTo A) (P.restrictTo_integrable_maximum A hP) (knownInState known A)
      (y := fun a j l => a (stateEmbedding A j,l)) (w := fun _ => 1) (c := fun _ => c)
      (fun j l => measurable_pi_apply (stateEmbedding A j,l)) measurable_const measurable_const
      (fun _ => zero_lt_one) (fun _ => hc0)
  have hm : Measurable (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      ∑ A : Finset (Fin n), if ProphetSecretary.Probability.pendingClockSet t q.2 = A then F A q.1 else 0) := by
    apply Finset.measurable_sum
    intro A _
    exact Measurable.ite
      (measurableSet_eq_fun ((ProphetSecretary.Probability.measurable_pendingClockSet t).comp measurable_snd) measurable_const)
      ((hF A).comp measurable_fst) measurable_const
  have heq : (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
        (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z) =
      (fun q => ∑ A : Finset (Fin n), if ProphetSecretary.Probability.pendingClockSet t q.2 = A then F A q.1 else 0) := by
    funext q
    have hs : (∑ A : Finset (Fin n), if ProphetSecretary.Probability.pendingClockSet t q.2 = A then F A q.1 else 0) =
        F (ProphetSecretary.Probability.pendingClockSet t q.2) q.1 := by
      rw [Finset.sum_eq_single (ProphetSecretary.Probability.pendingClockSet t q.2)]
      · exact if_pos rfl
      · intro A _ hA
        exact if_neg (Ne.symm hA)
      · simp
    rw [hs]
    unfold Instance.continuationValue
    rw [mixedEmpiricalInstance_restrictTo]
    rfl
  rw [heq]
  exact hm

lemma Instance.measurable_mixedPendingValueError (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (t z : ℝ) (hz : 0 ≤ z) :
    Measurable (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z|) := by
  have hQ := measurable_mixedPendingValue (n := n) (k := k) P hP known t z hz
  have hP := (measurable_of_finite (fun A : Finset (Fin n) => P.continuationValue A (max 0 (1-t)) 1 z)).comp
    ((ProphetSecretary.Probability.measurable_pendingClockSet t).comp
      (measurable_snd : Measurable (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))))
  exact (continuous_abs.comp_stronglyMeasurable (hQ.sub hP).stronglyMeasurable).measurable

end ProphetSecretary.Model
