import ProphetSecretary.Probability.GridCollisions
import ProphetSecretary.Probability.CountedMedian
import ProphetSecretary.Model.ArrivalRepresentation
import Mathlib.Data.List.FinRange

/-!
# Sorted dyadic arrival times

Downward rounding is monotone, so it commutes with sorting the clock values.
The times are sorted independently of the exogenous order. Coincident grid
times therefore do not change that order.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability
open ProphetSecretary.Model

lemma monotone_uniformGridIndex (N : ℕ) (hN : 0 < N) : Monotone (uniformGridIndex N hN) := by
  intro a b hab
  exact min_le_min le_rfl (Nat.floor_mono (mul_le_mul_of_nonneg_left hab (by positivity)))

lemma monotone_uniformGridRound (N : ℕ) (hN : 0 < N) : Monotone (uniformGridRound N hN) := by
  intro a b hab
  exact div_le_div_of_nonneg_right (by exact_mod_cast monotone_uniformGridIndex N hN hab) (by positivity)

def countedSortVector {α : Type*} [LinearOrder α] {n : ℕ} (x : Fin n → α) : (Fin n → α) × ℕ :=
  let q := countedInsertionSort (· ≤ ·) (List.ofFn x)
  (fun i => q.1.get ⟨i.val, by simp [q, countedInsertionSort_value, List.length_insertionSort]⟩,
    q.2)

lemma countedSortVector_work {α : Type*} [LinearOrder α] {n : ℕ} (x : Fin n → α) :
    (countedSortVector x).2 ≤ 4*(n+1)^2 := by
  simpa [countedSortVector] using countedInsertionSort_work (· ≤ ·) (List.ofFn x)

lemma countedSortVector_eq_of_sorted_permutation {α : Type*} [LinearOrder α] {n : ℕ}
    (x : Fin n → α) (p : Equiv.Perm (Fin n)) (h : Monotone (x ∘ p)) :
    (countedSortVector x).1 = x ∘ p := by
  let q := countedInsertionSort (· ≤ ·) (List.ofFn x)
  have hSort : q.1.SortedLE := by rw [countedInsertionSort_value]; exact List.sortedLE_insertionSort
  have hPerm : List.Perm q.1 (List.ofFn (x ∘ p)) := by
    rw [countedInsertionSort_value]
    exact (List.perm_insertionSort _ _).trans (p.ofFn_comp_perm x).symm
  have hList := hPerm.eq_of_sortedLE hSort h.sortedLE_ofFn
  funext i
  have he := congrArg (fun l : List α => l[i.val]?) hList
  have h1 : i.val < q.1.length := by rw [hList, List.length_ofFn]; exact i.isLt
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem (by simp)] at he
  have hget := Option.some.inj he
  simpa only [countedSortVector, List.get_eq_getElem, List.getElem_ofFn, Fin.eta] using hget

noncomputable def sortedGridValues {n : ℕ} (N : ℕ) (x : Fin n → Fin N) : Fin n → ℝ :=
  fun i => gridPoint N ((countedSortVector x).1 i)

lemma sortedGridValues_eq_round_sorted {n N : ℕ} (hN : 0 < N) (u : Fin n → ℝ)
    (hu : Function.Injective u) :
    sortedGridValues N (fun i => uniformGridIndex N hN (u i)) =
      fun i => uniformGridRound N hN (Instance.sortedClocks u i) := by
  have hp := (Instance.hasArrivalOrder_arrivalPermutation hu).monotone
  have h := countedSortVector_eq_of_sorted_permutation (fun i => uniformGridIndex N hN (u i))
    (Instance.arrivalPermutation u) ((monotone_uniformGridIndex N hN).comp hp)
  unfold sortedGridValues
  simp only [h, Function.comp_apply, Instance.sortedClocks, if_pos hu, uniformGridRound]

noncomputable def roundedSortedTimesLaw (n N : ℕ) (hN : 0 < N) : Measure (Fin n → ℝ) :=
  ((Instance.clocksLaw n).map Instance.sortedClocks).map (fun s i => uniformGridRound N hN (s i))

lemma measurable_roundTimeVector (n N : ℕ) (hN : 0 < N) :
    Measurable (fun s : Fin n → ℝ => fun i => uniformGridRound N hN (s i)) :=
  measurable_pi_iff.mpr (fun i => (measurable_uniformGridRound N hN).comp (measurable_pi_apply i))

instance roundedSortedTimesLaw_probability (n N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (roundedSortedTimesLaw n N hN) := by
  haveI : IsProbabilityMeasure ((Instance.clocksLaw n).map Instance.sortedClocks) :=
    Measure.isProbabilityMeasure_map Instance.measurable_sortedClocks.aemeasurable
  exact Measure.isProbabilityMeasure_map (measurable_roundTimeVector n N hN).aemeasurable

theorem map_sortedGridValues (n N : ℕ) (hN : 0 < N) :
    (gridIndexVectorLaw n N hN).map (sortedGridValues (n := n) N) = roundedSortedTimesLaw n N hN := by
  have hp := measurePreserving_gridIndexVector n N hN
  rw [← hp.map_eq, roundedSortedTimesLaw,
    Measure.map_map (measurable_of_countable _) hp.measurable,
    Measure.map_map (measurable_roundTimeVector n N hN) Instance.measurable_sortedClocks]
  apply Measure.map_congr
  filter_upwards [Instance.clocks_pairwise_distinct (n := n)] with u hu
  exact sortedGridValues_eq_round_sorted hN u hu

/-- A fair-bit clock reservoir uses `nb` bits and sorts the resulting indices
before converting to rational timestamps. -/
def countedDyadicSortedClocks {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) :
    (Fin n → ℚ) × (ℕ × ℕ) :=
  let q := countedSortVector (fun i => (countedFairBitsIndex b (bits i)).1)
  (fun i => gridPoint (2^b) (q.1 i),
    (Finset.univ.sum fun i : Fin n => (countedFairBitsIndex b (bits i)).2, q.2))

lemma countedDyadicSortedClocks_reads_work {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) :
    (countedDyadicSortedClocks b bits).2.1 = n*b ∧
      (countedDyadicSortedClocks b bits).2.2 ≤ 4*(n+1)^2 := by
  exact ⟨by simp [countedDyadicSortedClocks, countedFairBitsIndex_reads], countedSortVector_work _⟩

theorem map_countedDyadicSortedClocks (n b : ℕ) :
    (Measure.pi (fun _ : Fin n => fairBitVectorLaw b)).map
      (fun bits i => (((countedDyadicSortedClocks b bits).1 i : ℚ):ℝ)) =
      roundedSortedTimesLaw n (2^b) (by positivity) := by
  have hp := measurePreserving_fairIndexVector n b
  rw [← map_sortedGridValues n (2^b) (by positivity), ← hp.map_eq,
    Measure.map_map (measurable_of_countable _) hp.measurable]
  congr 1
  funext bits i
  simp only [countedDyadicSortedClocks, sortedGridValues, Function.comp_apply,
    countedFairBitsIndex_value, gridPoint_ratCast]

/-- Joint law when the online permutation is exogenous and independent of
the fair-bit clock reservoir. -/
theorem measurePreserving_dyadicSortedClocks_withPermutation (n b : ℕ) :
    MeasurePreserving (fun q : (Fin n → Fin b → Bool) × Equiv.Perm (Fin n) =>
      ((fun i => (((countedDyadicSortedClocks b q.1).1 i : ℚ):ℝ)),q.2))
      ((Measure.pi (fun _ : Fin n => fairBitVectorLaw b)).prod (Instance.uniformPermutationLaw n))
      ((roundedSortedTimesLaw n (2^b) (by positivity)).prod (Instance.uniformPermutationLaw n)) :=
  (MeasurePreserving.mk (measurable_of_countable _) (map_countedDyadicSortedClocks n b)).prod
    (MeasurePreserving.id _)

end ProphetSecretary.Probability
