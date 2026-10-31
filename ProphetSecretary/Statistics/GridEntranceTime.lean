import ProphetSecretary.Statistics.TrueCriticalEntrance
import ProphetSecretary.Statistics.GridCriticalPrefixes
import ProphetSecretary.Statistics.DyadicEntranceGrid

/-!
# Actual grid entrance times converge to the true entrance

The first critical grid event determines an elapsed time; if no event occurs,
the terminal convention is one. Finer dyadic grids approach the measurable true
critical entrance from above. The proof uses monotonicity and actual grid
density, without asserting convergence of any online policy.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.gridEntranceTime (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ) (N : ℕ)
    (u : Fin n → ℝ) : ℝ :=
  if ∃ j<N, P.firstCriticalGridEvent τ hi a j u then
    ∑ j ∈ Finset.range N, if P.firstCriticalGridEvent τ hi a j u then τ j else 0 else 1

lemma Instance.gridEntranceTime_eq_of_event (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ)
    {j N : ℕ} (hj : j<N) (u : Fin n → ℝ) (hE : P.firstCriticalGridEvent τ hi a j u) :
    P.gridEntranceTime τ hi a N u = τ j := by
  unfold gridEntranceTime
  rw [if_pos ⟨j,hj,hE⟩,Finset.sum_eq_single j]
  · exact if_pos hE
  · intro l _ hlj
    exact if_neg (fun hl => hlj (P.firstCriticalGridEvent_unique τ hi a u hl hE))
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hj))

lemma Instance.gridEntranceTime_eq_one_of_no_event (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ)
    (N : ℕ) (u : Fin n → ℝ) (hE : ¬∃ j<N, P.firstCriticalGridEvent τ hi a j u) :
    P.gridEntranceTime τ hi a N u = 1 := if_neg hE

lemma Instance.exists_firstCriticalGridEvent_of_critical (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ)
    {j N : ℕ} (hj : j<N) (u : Fin n → ℝ)
    (hcrit : P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ j) u) (1-τ j) 1 hi ≤ a) :
    ∃ l<N, P.firstCriticalGridEvent τ hi a l u ∧ l≤j := by
  have hex : ∃ l, l<N ∧ P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ l) u) (1-τ l) 1 hi ≤ a :=
    ⟨j,hj,hcrit⟩
  let l := Nat.find hex
  have hlN : l<N := (Nat.find_spec hex).1
  have hlc := (Nat.find_spec hex).2
  refine ⟨l,hlN,⟨hlc,?_⟩,Nat.find_min' hex ⟨hj,hcrit⟩⟩
  intro r hrl hrc
  have hrN : r<N := hrl.trans hlN
  exact (not_le.mpr hrl) (Nat.find_min' hex ⟨hrN,hrc⟩)

lemma Instance.gridEntranceTime_le_of_critical (P : Instance n) (τ : ℕ → ℝ) (hτ : Monotone τ) (hi a : ℝ)
    {j N : ℕ} (hj : j<N) (u : Fin n → ℝ)
    (hcrit : P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ j) u) (1-τ j) 1 hi ≤ a) :
    P.gridEntranceTime τ hi a N u ≤ τ j := by
  obtain ⟨l,hl,hE,hlj⟩ := P.exists_firstCriticalGridEvent_of_critical τ hi a hj u hcrit
  rw [P.gridEntranceTime_eq_of_event τ hi a hl u hE]
  exact hτ hlj

lemma Instance.gridEntranceTime_mem (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ) (N : ℕ)
    (hTimes : ∀ j<N, τ j ∈ Icc (0 : ℝ) 1) (u : Fin n → ℝ) :
    P.gridEntranceTime τ hi a N u ∈ Icc (0 : ℝ) 1 := by
  by_cases hex : ∃ j<N, P.firstCriticalGridEvent τ hi a j u
  · obtain ⟨j,hj,hE⟩ := hex
    rw [P.gridEntranceTime_eq_of_event τ hi a hj u hE]
    exact hTimes j hj
  · rw [P.gridEntranceTime_eq_one_of_no_event τ hi a N u hex]
    exact ⟨zero_le_one,le_rfl⟩

lemma Instance.trueCriticalEntrance_le_gridTime (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (τ : ℕ → ℝ) {hi a : ℝ} (hhi : 0 ≤ hi)
    (N : ℕ) (hTimes : ∀ j<N, τ j ∈ Icc (0 : ℝ) 1) (u : Fin n → ℝ) :
    P.trueCriticalEntrance hi a u ≤ P.gridEntranceTime τ hi a N u := by
  by_cases hex : ∃ j<N, P.firstCriticalGridEvent τ hi a j u
  · obtain ⟨j,hj,hE⟩ := hex
    rw [P.gridEntranceTime_eq_of_event τ hi a hj u hE]
    exact P.trueCriticalEntrance_le_of_critical hP hhi u (hTimes j hj).1 (hTimes j hj).2 hE.1
  · rw [P.gridEntranceTime_eq_one_of_no_event τ hi a N u hex]
    exact (P.trueCriticalEntrance_mem hi a u).2

/-- Dyadic entrance times approach the actual first critical state from above. -/
theorem Instance.dyadic_gridEntranceTime_tendsto (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a : ℝ} (hhi : 0 ≤ hi) (u : Fin n → ℝ) :
    Tendsto (fun m => P.gridEntranceTime (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a (2^m) u)
      atTop (𝓝 (P.trueCriticalEntrance hi a u)) := by
  have hTimes (m j : ℕ) : ProphetSecretary.Statistics.dyadicEntranceGrid m j ∈ Icc (0 : ℝ) 1 :=
    ⟨(ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j).1,(ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j).2.le⟩
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun m => hb.trans_le
      (P.trueCriticalEntrance_le_gridTime hP _ hhi _ (fun j _ => hTimes m j) u)
  · intro b hb
    by_cases hb1 : 1<b
    · exact Eventually.of_forall fun m =>
        (P.gridEntranceTime_mem _ hi a _ (fun j _ => hTimes m j) u).2.trans_lt hb1
    · have hb1' : b≤1 := le_of_not_gt hb1
      have hD := ProphetSecretary.Statistics.eventually_dyadicEntranceGrid_between
        (P.trueCriticalEntrance_mem hi a u).1 hb hb1'
      filter_upwards [hD] with m hm
      obtain ⟨j,hj,hσj,hjb⟩ := hm
      have hcrit := P.critical_after_trueEntrance hP hhi u hσj (hTimes m j).2
      have hle := P.gridEntranceTime_le_of_critical _
        (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) hi a hj u hcrit
      exact hle.trans_lt hjb

end ProphetSecretary.Model
