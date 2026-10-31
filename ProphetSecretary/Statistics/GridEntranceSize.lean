import ProphetSecretary.Statistics.GridCriticalPrefixes
import ProphetSecretary.Statistics.RemainingSize

/-!
# Grid entrance size without a grid-cardinality loss

True criticality forces an entrance to occur after elapsed time 1−a/hi.
Remaining size is decreasing on every clock path, and only one first-entrance
event can occur. Deterministic-time expectation therefore bounds the sum of
all entrance size multipliers by a(1+S)/hi, independently of the grid.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

omit [NeZero k] in
lemma Instance.firstCriticalGridEvent_time_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (τ : ℕ → ℝ) {hi a : ℝ} (hhi : 0 < hi)
    (j : ℕ) (ht1 : τ j ≤ 1) (u : Fin n → ℝ) (hE : P.firstCriticalGridEvent τ hi a j u) :
    1-a/hi ≤ τ j := by
  have hv := P.durationWeight_le_continuationValue hP (ProphetSecretary.Probability.pendingClockSet (τ j) u)
    (sub_nonneg.mpr ht1) (by norm_num : (0 : ℝ) ≤ 1) hhi.le
  have hnum : (1-τ j)*hi ≤ a := by nlinarith only [hv,hE.1]
  have h := (le_div_iff₀ hhi).mpr hnum
  linarith only [h]

omit [NeZero k] in
lemma Instance.gridEntranceSizeMultiplier_integrable (P : Instance n) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (hi a : ℝ) (j : ℕ) (ht0 : 0 ≤ τ j) (ht1 : τ j ≤ 1) :
    Integrable (P.gridEntranceSizeMultiplier (k := k) τ hi a j)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hm := (P.stronglyMeasurable_gridEntranceSizeMultiplier (k := k) τ hτ hi a j).mono
    (ProphetSecretary.Probability.observedClockSigma_le (τ j))
  apply Integrable.of_bound hm.aestronglyMeasurable (P.totalFirstMoment+1)
  exact Eventually.of_forall fun q => by
    have h := P.gridEntranceSizeMultiplier_mem (k := k) τ hi a j ht0 ht1 q
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

omit [NeZero k] in
lemma Instance.sum_gridEntranceSizeMultiplier_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (τ : ℕ → ℝ) {hi a : ℝ} (hhi : 0 < hi) (ha : 0 ≤ a)
    (N : ℕ) (hTimes : ∀ j < N, τ j ∈ Icc (0 : ℝ) 1)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    (∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q) ≤
      P.remainingSize (max 0 (1-a/hi)) q.2 := by
  let r := max 0 (1-a/hi)
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r ≤ 1 := max_le zero_le_one (by have := div_nonneg ha hhi.le; linarith)
  have hsingle (j : ℕ) (hj : j ∈ Finset.range N) : P.gridEntranceSizeMultiplier τ hi a j q ≤ P.remainingSize r q.2 := by
    by_cases hE : P.firstCriticalGridEvent τ hi a j q.2
    · have hjt := hTimes j (Finset.mem_range.mp hj)
      have hl := P.firstCriticalGridEvent_time_lower hP τ hhi j hjt.2 q.2 hE
      have hrj : r ≤ τ j := max_le hjt.1 hl
      change (if P.firstCriticalGridEvent τ hi a j q.2 then P.remainingSize (τ j) q.2 else 0) ≤ _
      rw [if_pos hE]
      exact P.remainingSize_antitone q.2 hrj
    · change (if P.firstCriticalGridEvent τ hi a j q.2 then P.remainingSize (τ j) q.2 else 0) ≤ _
      rw [if_neg hE]
      exact (P.observedRemainingSize_mem hr0 hr1 q.2).1
  by_cases hex : ∃ j ∈ Finset.range N, P.firstCriticalGridEvent τ hi a j q.2
  · obtain ⟨j,hj,hE⟩ := hex
    rw [Finset.sum_eq_single j]
    · exact hsingle j hj
    · intro l _ hlj
      have hn : ¬P.firstCriticalGridEvent τ hi a l q.2 := fun hl =>
        hlj (P.firstCriticalGridEvent_unique τ hi a q.2 hl hE)
      exact if_neg hn
    · intro hn
      exact False.elim (hn hj)
  · have hz : ∀ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q = 0 := by
      intro j hj
      exact if_neg (fun hE => hex ⟨j,hj,hE⟩)
    rw [Finset.sum_eq_zero hz]
    exact (P.observedRemainingSize_mem hr0 hr1 q.2).1

omit [NeZero k] in
/-- Finite-grid version of `upstat:entrance`, uniform over the grid size. -/
theorem Instance.integral_gridEntranceSize_sum_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (τ : ℕ → ℝ) (hτ : Monotone τ)
    {hi a : ℝ} (hhi : 0 < hi) (ha : 0 ≤ a) (N : ℕ)
    (hTimes : ∀ j < N, τ j ∈ Icc (0 : ℝ) 1) :
    (∫ q, ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier (k := k) τ hi a j q
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤ a * (1+P.totalFirstMoment) / hi := by
  let r := max 0 (1-a/hi)
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r ≤ 1 := max_le zero_le_one (by have := div_nonneg ha hhi.le; linarith)
  have hSum : Integrable (fun q => ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier (k := k) τ hi a j q)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) :=
    integrable_finsetSum _ fun j hj => P.gridEntranceSizeMultiplier_integrable τ hτ hi a j
      (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2
  have hp : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (Instance.clocksLaw n) := measurePreserving_snd
  have hR := hp.integrable_comp_of_integrable (P.integrable_remainingSize hr0 hr1)
  have hmean := integral_mono hSum hR (fun q => P.sum_gridEntranceSizeMultiplier_le hP τ hhi ha N hTimes q)
  have heq := integral_map (μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    hp.measurable.aemeasurable (P.measurable_remainingSize r).aestronglyMeasurable
  rw [hp.map_eq] at heq
  have hRmean : (∫ q, P.remainingSize r q.2 ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) =
      (1-r) * (P.totalFirstMoment+1) := heq.symm.trans (P.integral_remainingSize hr0 hr1)
  apply (hmean.trans_eq hRmean).trans
  have hr : 1-r ≤ a/hi := by dsimp [r]; linarith only [le_max_right (0 : ℝ) (1-a/hi)]
  have hb := mul_le_mul_of_nonneg_right hr (by linarith [P.totalFirstMoment_nonnegative] : 0 ≤ P.totalFirstMoment+1)
  exact hb.trans_eq (by ring)

end ProphetSecretary.Model
