import ProphetSecretary.Statistics.ObservedCriticalPrefixes
import ProphetSecretary.Probability.PendingStateRightLimit
import ProphetSecretary.Probability.RationalObservationTimes
import ProphetSecretary.Model.ClockContinuationOrder

/-!
# True-law critical entrance time

The infimum over a fixed dense countable grid defines a measurable entrance
using only true laws and clocks. Monotonicity identifies it with the first
critical state, including downward arrival jumps through the post-arrival
right limit. Waiting bounds its remaining horizon without optional stopping.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.criticalClockTimeCandidate (P : Instance n) (hi a : ℝ) (u : Fin n → ℝ) (j : ℕ) : ℝ :=
  let t := ProphetSecretary.Probability.rationalObservationTime j
  if P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi ≤ a then t else 1

noncomputable def Instance.trueCriticalEntrance (P : Instance n) (hi a : ℝ) (u : Fin n → ℝ) : ℝ :=
  ⨅ j, P.criticalClockTimeCandidate hi a u j

lemma Instance.criticalClockTimeCandidate_mem (P : Instance n) (hi a : ℝ) (u : Fin n → ℝ) (j : ℕ) :
    P.criticalClockTimeCandidate hi a u j ∈ Icc (0 : ℝ) 1 := by
  unfold criticalClockTimeCandidate
  dsimp only
  split_ifs
  · have h := ProphetSecretary.Probability.rationalObservationTime_mem j
    exact ⟨h.1,h.2.le⟩
  · exact ⟨zero_le_one,le_rfl⟩

lemma Instance.trueCriticalEntrance_mem (P : Instance n) (hi a : ℝ) (u : Fin n → ℝ) :
    P.trueCriticalEntrance hi a u ∈ Icc (0 : ℝ) 1 := by
  have hb : BddBelow (range (P.criticalClockTimeCandidate hi a u)) :=
    ⟨0,by rintro _ ⟨j,rfl⟩; exact (P.criticalClockTimeCandidate_mem hi a u j).1⟩
  exact ⟨le_ciInf fun j => (P.criticalClockTimeCandidate_mem hi a u j).1,
    (ciInf_le hb 0).trans (P.criticalClockTimeCandidate_mem hi a u 0).2⟩

lemma Instance.measurable_trueCriticalEntrance (P : Instance n) (hi a : ℝ) :
    Measurable (P.trueCriticalEntrance hi a) := by
  apply Measurable.iInf
  intro j
  let t := ProphetSecretary.Probability.rationalObservationTime j
  have hV : Measurable (fun u : Fin n → ℝ =>
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi) :=
    (measurable_of_finite (fun A : Finset (Fin n) => P.continuationValue A (1-t) 1 hi)).comp
      (ProphetSecretary.Probability.measurable_pendingClockSet t)
  exact Measurable.ite (measurableSet_le hV measurable_const) measurable_const measurable_const

lemma Instance.trueCriticalEntrance_le_of_critical (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a t : ℝ} (hhi : 0 ≤ hi)
    (u : Fin n → ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcrit : P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi ≤ a) :
    P.trueCriticalEntrance hi a u ≤ t := by
  by_contra hnot
  have hlt : t < P.trueCriticalEntrance hi a u := lt_of_not_ge hnot
  obtain ⟨q,hqt,hqσ⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℝ) ≤ q := ht0.trans hqt.le
  have hq1 : (q : ℝ) < 1 := hqσ.trans_le (P.trueCriticalEntrance_mem hi a u).2
  have heq := ProphetSecretary.Probability.rationalObservationTime_covers q ⟨hq0,hq1⟩
  have hqc : P.continuationValue (ProphetSecretary.Probability.pendingClockSet (q : ℝ) u) (1-(q : ℝ)) 1 hi ≤ a :=
    ((P.clockContinuation_antitone hP hhi u) ht1 hq1.le hqt.le).trans hcrit
  have hb : BddBelow (range (P.criticalClockTimeCandidate hi a u)) :=
    ⟨0,by rintro _ ⟨j,rfl⟩; exact (P.criticalClockTimeCandidate_mem hi a u j).1⟩
  have hσ := ciInf_le hb (Encodable.encode q)
  change P.trueCriticalEntrance hi a u ≤ P.criticalClockTimeCandidate hi a u (Encodable.encode q) at hσ
  have hval : P.criticalClockTimeCandidate hi a u (Encodable.encode q) = q := by
    unfold criticalClockTimeCandidate
    rw [heq,if_pos hqc]
  rw [hval] at hσ
  exact (not_le.mpr hqσ) hσ

lemma Instance.critical_after_trueEntrance (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a t : ℝ} (hhi : 0 ≤ hi)
    (u : Fin n → ℝ) (hσt : P.trueCriticalEntrance hi a u < t) (ht1 : t ≤ 1) :
    P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi ≤ a := by
  obtain ⟨j,hj⟩ := exists_lt_of_ciInf_lt hσt
  let r := ProphetSecretary.Probability.rationalObservationTime j
  have hcrit : P.continuationValue (ProphetSecretary.Probability.pendingClockSet r u) (1-r) 1 hi ≤ a := by
    by_contra hn
    change (if P.continuationValue (ProphetSecretary.Probability.pendingClockSet r u) (1-r) 1 hi ≤ a then r else 1) < t at hj
    rw [if_neg hn] at hj
    exact (not_lt_of_ge ht1) hj
  have hrt : r < t := by
    change (if P.continuationValue (ProphetSecretary.Probability.pendingClockSet r u) (1-r) 1 hi ≤ a then r else 1) < t at hj
    rw [if_pos hcrit] at hj
    exact hj
  exact ((P.clockContinuation_antitone hP hhi u) (ProphetSecretary.Probability.rationalObservationTime_mem j).2.le ht1 hrt.le).trans hcrit

/-- Waiting gives the exact horizon restriction used in `upstat:entrance`. -/
theorem Instance.trueCriticalEntrance_time_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a : ℝ} (hhi : 0 < hi) (ha : 0 ≤ a) (u : Fin n → ℝ) :
    1-a/hi ≤ P.trueCriticalEntrance hi a u := by
  apply le_ciInf
  intro j
  let t := ProphetSecretary.Probability.rationalObservationTime j
  unfold criticalClockTimeCandidate
  dsimp only
  split_ifs with hcrit
  · have hv := P.durationWeight_le_continuationValue hP (ProphetSecretary.Probability.pendingClockSet t u)
      (sub_nonneg.mpr (ProphetSecretary.Probability.rationalObservationTime_mem j).2.le) zero_le_one hhi.le
    have hn : (1-t)*hi ≤ a := by nlinarith only [hv,hcrit]
    have hh := (le_div_iff₀ hhi).mpr hn
    linarith only [hh]
  · have h := div_nonneg ha hhi.le
    linarith only [h]

/-- A downward-jump entrance is critical in its actual post-arrival state. -/
theorem Instance.trueCriticalEntrance_postcritical (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a : ℝ} (hhi : 0 ≤ hi) (u : Fin n → ℝ)
    (hσ1 : P.trueCriticalEntrance hi a u < 1) :
    P.continuationValue (ProphetSecretary.Probability.strictPendingClockSet (P.trueCriticalEntrance hi a u) u)
      (1-P.trueCriticalEntrance hi a u) 1 hi ≤ a := by
  let σ := P.trueCriticalEntrance hi a u
  have hlim := ProphetSecretary.Probability.pendingContinuationValue_tendsto_right P hP hhi u σ
  have hnear : ∀ᶠ t in 𝓝[>] σ, σ < t ∧ t ≤ 1 := by
    have h1 : ∀ᶠ t in 𝓝 σ, t < 1 := isOpen_Iio.mem_nhds hσ1
    filter_upwards [self_mem_nhdsWithin (a := σ) (s := Ioi σ),h1.filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht,ht1.le⟩
  have hbound : ∀ᶠ t in 𝓝[>] σ,
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 hi ≤ a := by
    filter_upwards [hnear] with t ht
    rw [max_eq_right (sub_nonneg.mpr ht.2)]
    exact P.critical_after_trueEntrance hP hhi u ht.1 ht.2
  have h := le_of_tendsto hlim hbound
  have hσ : σ ≤ 1 := hσ1.le
  rw [max_eq_right (sub_nonneg.mpr hσ)] at h
  exact h

end ProphetSecretary.Model
