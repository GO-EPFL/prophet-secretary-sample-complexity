import ProphetSecretary.Statistics.MixedGridEntranceVariables
import ProphetSecretary.Statistics.MixedStateFutureErrorDomination

/-!
# Actual mixed grid envelope dominates every later state

The single first-critical grid event selects an actual mixed state error. Its
common all-time/all-scalar comparison gives later-path domination, and actual
measurability and finite-dimensional bounds license subsequent Fatou arguments.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.mixedGridEntranceError_eq_of_event (P : Instance n) (known : Finset (Fin n)) (τ : ℕ → ℝ) (lo hi a : ℝ)
    {j N : ℕ} (hj : j<N) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)))
    (hE : P.firstCriticalGridEvent τ hi a j q.2) :
    P.mixedGridEntranceError known k τ lo hi a N q = P.mixedStateFutureError known k lo hi (τ j) q := by
  unfold mixedGridEntranceError
  rw [Finset.sum_eq_single j]
  · exact if_pos hE
  · intro l _ hlj
    exact if_neg (fun hl => hlj (P.firstCriticalGridEvent_unique τ hi a q.2 hl hE))
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hj))

lemma Instance.mixedGridEntranceError_nonnegative (P : Instance n) (known : Finset (Fin n)) (τ : ℕ → ℝ) (lo hi a : ℝ)
    (N : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : 0 ≤ P.mixedGridEntranceError known k τ lo hi a N q := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact P.mixedStateFutureError_nonnegative known lo hi (τ j) q
  · exact le_rfl

lemma Instance.measurable_mixedGridEntranceError (P : Instance n) (known : Finset (Fin n)) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (lo hi a : ℝ) (N : ℕ) : Measurable (P.mixedGridEntranceError known k τ lo hi a N) := by
  apply Finset.measurable_sum
  intro j _
  have hE := P.measurableSet_firstCriticalGridEvent (k := k) τ hτ hi a j
  have hm := ProphetSecretary.Probability.observedClockSigma_le (D := (Fin n × Fin k) → ℝ) (n := n) (τ j)
  exact Measurable.ite (hm _ hE) (P.measurable_mixedStateFutureError known lo hi (τ j)) measurable_const

lemma Instance.mixedGridEntranceError_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (τ : ℕ → ℝ) (lo hi a : ℝ) (N : ℕ)
    (hTimes : ∀ j<N, τ j ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), P.mixedGridEntranceError known k τ lo hi a N q ≤ 2*(n : ℝ) := by
  have hall : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ j<N, P.mixedStateFutureError known k lo hi (τ j) q ≤ 2*(n : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j<N
    · exact (P.mixedStateFutureError_bounded (k := k) known hbound lo hi (hTimes j hj).1 (hTimes j hj).2).mono fun q hq _ => hq
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hall] with q hq
  by_cases hex : ∃ j<N, P.firstCriticalGridEvent τ hi a j q.2
  · obtain ⟨j,hj,hE⟩ := hex
    rw [P.mixedGridEntranceError_eq_of_event known τ lo hi a hj q hE]
    exact hq j hj
  · have hz : P.mixedGridEntranceError known k τ lo hi a N q = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun hE => hex ⟨j,Finset.mem_range.mp hj,hE⟩)
    rw [hz]
    positivity

/-- All future times and scalar choices are controlled on the same event. -/
theorem Instance.mixedGridEntranceError_dominates_after_event (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (τ : ℕ → ℝ) (N : ℕ) (hTimes : ∀ j<N, τ j ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), ∀ j<N,
      P.firstCriticalGridEvent τ hi a j q.2 → ∀ t ∈ Icc (τ j) 1, ∀ z ∈ Icc lo hi,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.mixedGridEntranceError known k τ lo hi a N q := by
  have hall : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), ∀ j<N,
      ∀ t ∈ Icc (τ j) 1, ∀ z ∈ Icc lo hi,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.mixedStateFutureError known k lo hi (τ j) q := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j<N
    · exact (P.mixedStateFutureError_dominates_later (k := k) known hbound hlo hlohi (hTimes j hj).1 (hTimes j hj).2).mono
        fun q hq _ => hq
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hall] with q hq
  intro j hj hE t ht z hz
  rw [P.mixedGridEntranceError_eq_of_event known τ lo hi a hj q hE]
  exact hq j hj t ht z hz

end ProphetSecretary.Model
