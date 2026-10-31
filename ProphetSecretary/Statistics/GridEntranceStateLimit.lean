import ProphetSecretary.Statistics.GridArrivalNullSets
import ProphetSecretary.Statistics.GridStateStabilization
import ProphetSecretary.Statistics.GridEntranceVariables

/-!
# Convergence of actual grid entrance size to the post-arrival size

Grid times avoid arrivals almost surely and approach the true entrance from
above. The pending identity sets therefore stabilize to the strict post-arrival
set. The missing-grid-entrance convention contributes size zero at time one;
this uses absence of terminal clock atoms, not a reward-only value assumption.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators Topology

namespace ProphetSecretary.Model

variable {n k : ℕ}

lemma Instance.gridEntranceSize_eq_of_event (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ)
    {j N : ℕ} (hj : j<N) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)))
    (hE : P.firstCriticalGridEvent τ hi a j q.2) :
    P.gridEntranceSize k τ hi a N q = P.remainingSize (τ j) q.2 := by
  unfold gridEntranceSize
  rw [Finset.sum_eq_single j]
  · exact if_pos hE
  · intro l _ hlj
    exact if_neg (fun hl => hlj (P.firstCriticalGridEvent_unique τ hi a q.2 hl hE))
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hj))

lemma Instance.gridEntranceSize_eq_remainingSize_time (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ)
    (N : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (hu : ∀ i, q.2 i < 1) :
    P.gridEntranceSize k τ hi a N q = P.remainingSize (P.gridEntranceTime τ hi a N q.2) q.2 := by
  by_cases hex : ∃ j<N, P.firstCriticalGridEvent τ hi a j q.2
  · obtain ⟨j,hj,hE⟩ := hex
    rw [P.gridEntranceSize_eq_of_event τ hi a hj q hE,P.gridEntranceTime_eq_of_event τ hi a hj q.2 hE]
  · have hzero : P.gridEntranceSize k τ hi a N q = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun hE => hex ⟨j,Finset.mem_range.mp hj,hE⟩)
    have hA : ProphetSecretary.Probability.pendingClockSet 1 q.2 = ∅ := by
      apply Finset.ext
      intro i
      simpa [ProphetSecretary.Probability.mem_pendingClockSet] using not_le.mpr (hu i)
    have hR : P.remainingSize 1 q.2 = 0 := by
      unfold remainingSize
      rw [hA]
      simp [Instance.totalFirstMoment]
    rw [hzero,P.gridEntranceTime_eq_one_of_no_event τ hi a N q.2 hex,hR]

/-- Both the identity set and size converge under the actual independent clock
law. The array can be arbitrary because the entrance never uses training. -/
theorem Instance.dyadic_gridEntranceSize_tendsto_post (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a : ℝ} (hhi : 0 ≤ hi) :
    ∀ᵐ u : Fin n → ℝ ∂Instance.clocksLaw n, ∀ y : (Fin n × Fin k) → ℝ,
      Tendsto (fun m => P.gridEntranceSize k (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a (2^m) (y,u))
        atTop (𝓝 (P.postRemainingSize (P.trueCriticalEntrance hi a u) u)) := by
  have hU : ∀ᵐ u : Fin n → ℝ ∂Instance.clocksLaw n, ∀ i, u i < 1 := by
    filter_upwards [Instance.clocks_mem_unitInterval (n := n),clocks_avoid_dyadicEntranceGrid (n := n)] with u hu hn
    exact fun i => lt_of_le_of_ne (hu i).2 (hn.1 i)
  filter_upwards [hU,P.dyadic_gridEntranceTime_ne_arrivals hi a] with u hu hne
  intro y
  have hlim := P.dyadic_gridEntranceTime_tendsto (a := a) hP hhi u
  have hlower (m : ℕ) : P.trueCriticalEntrance hi a u ≤
      P.gridEntranceTime (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a (2^m) u :=
    P.trueCriticalEntrance_le_gridTime hP _ hhi _
      (fun j _ => ⟨(ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j).1,
        (ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j).2.le⟩) u
  have hB := P.remainingSize_tendsto_post u hlim hlower hne
  apply hB.congr'
  exact Eventually.of_forall fun m =>
    (P.gridEntranceSize_eq_remainingSize_time _ hi a (2^m) (y,u) hu).symm

end ProphetSecretary.Model
