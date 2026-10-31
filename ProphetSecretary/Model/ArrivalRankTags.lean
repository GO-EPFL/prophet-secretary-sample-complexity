import ProphetSecretary.Model.ArrivalRepresentation
import ProphetSecretary.Model.RankToClock
import ProphetSecretary.Probability.DependentIIDPermutation

/-!
# Independent tags indexed by chronological arrival rank

The rank is the number of strictly earlier arrivals on the tie-free event.
Permuting an independent identical tag array by those ranks preserves its
joint law with the clocks. The rank is therefore available causally from the
past count without revealing a construction label or future count.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model.Instance

noncomputable def arrivalRank {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : Fin n := (arrivalPermutation u).symm i

lemma measurable_arrivalRank {n : ℕ} (i : Fin n) : Measurable (fun u : Fin n → ℝ => arrivalRank u i) :=
  (measurable_of_countable (fun p : Equiv.Perm (Fin n) => p.symm i)).comp measurable_arrivalPermutation

lemma arrivalRank_counts_past {n : ℕ} {u : Fin n → ℝ} (hu : Function.Injective u) (i : Fin n) :
    (Finset.univ.filter (fun j : Fin n => u j<u i)).card=(arrivalRank u i).val := by
  have hOrder := hasArrivalOrder_arrivalPermutation hu
  have hLt (j : Fin n) : u j<u i ↔ (arrivalPermutation u).symm j<(arrivalPermutation u).symm i := by
    have h := hOrder.lt_iff_lt (a := (arrivalPermutation u).symm j) (b := (arrivalPermutation u).symm i)
    simpa only [Equiv.apply_symm_apply] using h
  have hFilter : Finset.univ.filter (fun j : Fin n => u j<u i)=
      Finset.univ.filter (fun j : Fin n => (arrivalPermutation u).symm j<(arrivalPermutation u).symm i) := by
    apply Finset.filter_congr
    intro j _
    exact hLt j
  rw [hFilter]
  exact card_filter_permutation_lt (arrivalPermutation u) ((arrivalPermutation u).symm i)

lemma arrivalRank_tags_measurePreserving {n : ℕ} {T : Type*} [MeasurableSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] :
    MeasurePreserving (fun z : (Fin n → ℝ) × (Fin n → T) => (z.1,fun i => z.2 (arrivalRank z.1 i)))
      ((clocksLaw n).prod (Measure.pi (fun _ : Fin n => κ)))
      ((clocksLaw n).prod (Measure.pi (fun _ : Fin n => κ))) :=
  ProphetSecretary.Probability.dependent_iid_reindex_measurePreserving (clocksLaw n) κ
    (fun u => (arrivalPermutation u).symm) (fun i => measurable_arrivalRank i)

end ProphetSecretary.Model.Instance
