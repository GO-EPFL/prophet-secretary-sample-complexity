import ProphetSecretary.Statistics.GridEntranceTime

/-!
# Uniform clocks avoid all deterministic grid times

There are countably many dyadic grid points, and every clock has a non-atomic
uniform law. The actual first grid entrance is either one such point or the
terminal time, so it almost surely coincides with no arrival, despite depending
on the same clock vector.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma clocks_avoid_dyadicEntranceGrid :
    ∀ᵐ u : Fin n → ℝ ∂Instance.clocksLaw n,
      (∀ i, u i ≠ 1) ∧ ∀ m j i, u i ≠ ProphetSecretary.Statistics.dyadicEntranceGrid m j := by
  have h1 : ∀ᵐ u : Fin n → ℝ ∂Instance.clocksLaw n, ∀ i, u i ≠ 1 :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i).quasiMeasurePreserving.ae
      (Instance.uniformClock.ae_ne 1)
  have h2 : ∀ᵐ u : Fin n → ℝ ∂Instance.clocksLaw n, ∀ m j i,
      u i ≠ ProphetSecretary.Statistics.dyadicEntranceGrid m j :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun j => ae_all_iff.mpr fun i =>
      (measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i).quasiMeasurePreserving.ae
        (Instance.uniformClock.ae_ne (ProphetSecretary.Statistics.dyadicEntranceGrid m j))
  exact h1.and h2

lemma Instance.dyadic_gridEntranceTime_ne_arrivals (P : Instance n) (hi a : ℝ) :
    ∀ᵐ u : Fin n → ℝ ∂Instance.clocksLaw n, ∀ m i,
      P.gridEntranceTime (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a (2^m) u ≠ u i := by
  filter_upwards [clocks_avoid_dyadicEntranceGrid (n := n)] with u hu
  intro m i
  by_cases hex : ∃ j<2^m, P.firstCriticalGridEvent (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a j u
  · obtain ⟨j,hj,hE⟩ := hex
    rw [P.gridEntranceTime_eq_of_event _ hi a hj u hE]
    exact Ne.symm (hu.2 m j i)
  · rw [P.gridEntranceTime_eq_one_of_no_event _ hi a _ u hex]
    exact Ne.symm (hu.1 i)

end ProphetSecretary.Model
