import ProphetSecretary.Statistics.EntranceFutureMoments

/-!
# Expected size at the actual true critical entrance

Waiting forces σ_a≥1−a/hi. Both the post-arrival remaining size and the inclusive
remaining size at σ_a are therefore dominated by the size at the deterministic
cutoff max(0,1−a/hi). Uniform-clock expectation proves `upstat:entrance` directly,
without an optional-stopping or independence hypothesis.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.entranceRemainingSize_le_cutoff (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a : ℝ} (hhi : 0<hi) (ha : 0≤a) (u : Fin n → ℝ) :
    P.entranceRemainingSize hi a u ≤ P.remainingSize (max 0 (1-a/hi)) u := by
  let σ := P.trueCriticalEntrance hi a u
  have hsub : ProphetSecretary.Probability.strictPendingClockSet σ u ⊆ ProphetSecretary.Probability.pendingClockSet σ u := by
    intro i hi
    exact (ProphetSecretary.Probability.mem_pendingClockSet σ u i).mpr
      ((ProphetSecretary.Probability.mem_strictPendingClockSet σ u i).mp hi).le
  have hmono := P.totalFirstMoment_restrictTo_mono hsub
  have hPL : P.postRemainingSize σ u ≤ P.remainingSize σ u := add_le_add hmono le_rfl
  have hσ0 : 0≤σ := (P.trueCriticalEntrance_mem hi a u).1
  have hσr : 1-a/hi≤σ := P.trueCriticalEntrance_time_lower hP hhi ha u
  have hrσ : max 0 (1-a/hi)≤σ := max_le hσ0 hσr
  exact hPL.trans (P.remainingSize_antitone u hrσ)

lemma Instance.integrable_entranceRemainingSize (P : Instance n) (hi a : ℝ) :
    Integrable (P.entranceRemainingSize hi a) (Instance.clocksLaw n) := by
  apply Integrable.of_bound (P.measurable_entranceRemainingSize hi a).aestronglyMeasurable (P.totalFirstMoment+1)
  exact Eventually.of_forall fun u => by
    have h := P.entranceRemainingSize_mem hi a u
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2

/-- `upstat:entrance` for the actual measurable first critical state. -/
theorem Instance.integral_entranceRemainingSize_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a : ℝ} (hhi : 0<hi) (ha : 0≤a) :
    (∫ u, P.entranceRemainingSize hi a u ∂Instance.clocksLaw n) ≤ a*(1+P.totalFirstMoment)/hi := by
  let r := max 0 (1-a/hi)
  have hr0 : 0≤r := le_max_left _ _
  have hr1 : r≤1 := max_le zero_le_one (by have := div_nonneg ha hhi.le; linarith)
  have hm := integral_mono (P.integrable_entranceRemainingSize hi a) (P.integrable_remainingSize hr0 hr1)
    (fun u => P.entranceRemainingSize_le_cutoff hP hhi ha u)
  rw [P.integral_remainingSize hr0 hr1] at hm
  apply hm.trans
  have hr : 1-r≤a/hi := by dsimp [r]; linarith only [le_max_right (0:ℝ) (1-a/hi)]
  have hbound := mul_le_mul_of_nonneg_right hr (by linarith [P.totalFirstMoment_nonnegative] : 0≤P.totalFirstMoment+1)
  exact hbound.trans_eq (by ring)

end ProphetSecretary.Model
