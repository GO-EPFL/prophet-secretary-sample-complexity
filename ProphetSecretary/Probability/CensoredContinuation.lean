import ProphetSecretary.Probability.CensoredClockConditioning
import ProphetSecretary.Statistics.ResidualContinuationBound

/-!
# The actual continuation represented by refreshed pending clocks

The unseen set is determined by elapsed clock observations. Its observed prefix
retains identities, times, and values, including zeros. Refreshing pending clocks
is exactly the existing continuation construction after this prefix.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def pendingClockSet (t : ℝ) (u : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => t ≤ u i

lemma mem_pendingClockSet (t : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    i ∈ pendingClockSet t u ↔ t ≤ u i := by simp only [pendingClockSet, Finset.mem_filter, Finset.mem_univ, true_and]

lemma validPrefix_pendingClockSet (t : ℝ) (x u : Fin n → ℝ) :
    Model.ValidPrefix (pendingClockSet t u) t (Model.history Finset.univ x u t) := by
  constructor
  · intro i hi
    have htime := (mem_pendingClockSet t u i).mp hi
    simp only [Model.history, Finset.mem_univ, true_and, if_neg (not_lt.mpr htime)]
  · intro i hi
    have htime : u i < t := lt_of_not_ge (fun h => hi ((mem_pendingClockSet t u i).mpr h))
    exact ⟨u i, x i, by simp only [Model.history, Finset.mem_univ, true_and, if_pos htime], htime.le⟩

lemma refreshClocks_eq_extendClocks (t : ℝ) (x u v : Fin n → ℝ) :
    refreshClocks t (u,v) = Model.extendClocks (pendingClockSet t u) t (Model.history Finset.univ x u t)
      (v ∘ Model.stateEmbedding (pendingClockSet t u)) := by
  funext i
  by_cases hi : i ∈ pendingClockSet t u
  · have htime := (mem_pendingClockSet t u i).mp hi
    simp only [refreshClocks, refreshClock, if_neg (not_lt.mpr htime), Model.extendClocks,
      dif_pos hi, Function.comp_apply, Model.stateEmbedding_stateIndex]
    rfl
  · have htime : u i < t := lt_of_not_ge (fun h => hi ((mem_pendingClockSet t u i).mpr h))
    simp only [refreshClocks, refreshClock, Model.extendClocks, dif_neg hi,
      Model.history, Finset.mem_univ, true_and, if_pos htime, Model.observationTime]
    rfl

/-- Actual future-clock integration bounds the continuation's value error. -/
theorem abs_value_difference_pending_le_refreshEnvelope (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    {t w c : ℝ} (ht : t < 1) (hw : 0 < w) (hc : 0 ≤ c) (u : Fin n → ℝ) :
    |Q.continuationValue (pendingClockSet t u) (1-t) w c -
      P.continuationValue (pendingClockSet t u) (1-t) w c| ≤
      2 * ∫ v, Q.residualSuffixEnvelope P w c (refreshClocks t (u,v)) ∂Model.Instance.clocksLaw n := by
  have h := Q.abs_continuationValue_difference_le_extendedEnvelope P hQ hP (pendingClockSet t u)
    ht (Model.history Finset.univ (fun _ => 0) u t) (validPrefix_pendingClockSet t (fun _ => 0) u) hw hc
  simpa only [← refreshClocks_eq_extendClocks] using h

end ProphetSecretary.Probability
