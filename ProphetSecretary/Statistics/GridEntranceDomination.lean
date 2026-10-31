import ProphetSecretary.Statistics.GridEntranceVariables
import ProphetSecretary.Statistics.StateFutureErrorDomination

/-!
# A concrete grid entrance envelope controls every later state

Only one first critical grid event can occur. Its state-local error has the
proved common all-later/all-scalar domination under the actual product law.
The resulting grid error is measurable and bounded almost surely; the bound
by 2n is used only for integrability and subsequent limiting arguments.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.gridEntranceError_eq_of_event (P : Instance n) (τ : ℕ → ℝ) (lo hi a : ℝ)
    {j N : ℕ} (hj : j<N) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)))
    (hE : P.firstCriticalGridEvent τ hi a j q.2) :
    P.gridEntranceError k τ lo hi a N q = P.stateFutureError k lo hi (τ j) q := by
  unfold gridEntranceError
  rw [Finset.sum_eq_single j]
  · exact if_pos hE
  · intro l _ hlj
    exact if_neg (fun hl => hlj (P.firstCriticalGridEvent_unique τ hi a q.2 hl hE))
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hj))

lemma Instance.gridEntranceError_nonnegative (P : Instance n) (τ : ℕ → ℝ) (lo hi a : ℝ)
    (N : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : 0 ≤ P.gridEntranceError k τ lo hi a N q := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact P.stateFutureError_nonnegative lo hi (τ j) q
  · exact le_rfl

lemma Instance.measurable_gridEntranceError (P : Instance n) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (lo hi a : ℝ) (N : ℕ) : Measurable (P.gridEntranceError k τ lo hi a N) := by
  apply Finset.measurable_sum
  intro j _
  have hE := P.measurableSet_firstCriticalGridEvent (k := k) τ hτ hi a j
  have hm := ProphetSecretary.Probability.observedClockSigma_le (D := (Fin n × Fin k) → ℝ) (n := n) (τ j)
  exact Measurable.ite (hm _ hE) (P.measurable_stateFutureError lo hi (τ j)) measurable_const

lemma Instance.gridEntranceError_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (τ : ℕ → ℝ) (lo hi a : ℝ) (N : ℕ)
    (hTimes : ∀ j<N, τ j ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), P.gridEntranceError k τ lo hi a N q ≤ 2*(n : ℝ) := by
  have hall : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ j<N, P.stateFutureError k lo hi (τ j) q ≤ 2*(n : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j<N
    · exact (P.stateFutureError_bounded (k := k) hbound lo hi (hTimes j hj).1 (hTimes j hj).2).mono fun q hq _ => hq
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hall] with q hq
  by_cases hex : ∃ j<N, P.firstCriticalGridEvent τ hi a j q.2
  · obtain ⟨j,hj,hE⟩ := hex
    rw [P.gridEntranceError_eq_of_event τ lo hi a hj q hE]
    exact hq j hj
  · have hz : P.gridEntranceError k τ lo hi a N q = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun hE => hex ⟨j,Finset.mem_range.mp hj,hE⟩)
    rw [hz]
    positivity

/-- All future times and scalar choices are controlled on the same event. -/
theorem Instance.gridEntranceError_dominates_after_event (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (τ : ℕ → ℝ) (N : ℕ) (hTimes : ∀ j<N, τ j ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), ∀ j<N,
      P.firstCriticalGridEvent τ hi a j q.2 → ∀ t ∈ Icc (τ j) 1, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.gridEntranceError k τ lo hi a N q := by
  have hall : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), ∀ j<N,
      ∀ t ∈ Icc (τ j) 1, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.stateFutureError k lo hi (τ j) q := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j<N
    · exact (P.stateFutureError_dominates_later (k := k) hbound hlo hlohi (hTimes j hj).1 (hTimes j hj).2).mono
        fun q hq _ => hq
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hall] with q hq
  intro j hj hE t ht z hz
  rw [P.gridEntranceError_eq_of_event τ lo hi a hj q hE]
  exact hq j hj t ht z hz

end ProphetSecretary.Model
