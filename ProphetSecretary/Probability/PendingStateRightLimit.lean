import ProphetSecretary.Probability.PendingStateLeftLimit

/-!
# Post-arrival state as a right limit

The strict pending set excludes arrivals at the current time, representing the
state immediately after those observations. It is the right limit of the
strict-prefix unseen sets. The statement retains all original identities and
uses continuity of the true optimized value in the remaining weight.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def strictPendingClockSet (t : ℝ) (u : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => t < u i

lemma mem_strictPendingClockSet (t : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    i ∈ strictPendingClockSet t u ↔ t < u i := by
  simp only [strictPendingClockSet, Finset.mem_filter, Finset.mem_univ, true_and]

lemma pendingClockSet_eventually_eq_right (u : Fin n → ℝ) (t : ℝ) :
    ∀ᶠ s in 𝓝[>] t, pendingClockSet s u = strictPendingClockSet t u := by
  have hall : ∀ᶠ s in 𝓝[>] t, ∀ i, s ≤ u i ↔ t < u i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : t < u i
    · have hh : ∀ᶠ s in 𝓝 t, s < u i := isOpen_Iio.mem_nhds hi
      filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with s hs
      exact ⟨fun _ => hi, fun _ => hs.le⟩
    · have hle : u i ≤ t := le_of_not_gt hi
      filter_upwards [self_mem_nhdsWithin (a := t) (s := Ioi t)] with s hs
      simp only [not_le.mpr (hle.trans_lt hs), hi]
  exact hall.mono fun s hs => Finset.ext fun i => by
    rw [mem_pendingClockSet, mem_strictPendingClockSet]
    exact hs i

/-- This represents a post-jump continuation without identifying a nonempty
zero-horizon reward value with zero. -/
theorem pendingContinuationValue_tendsto_right (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z)
    (u : Fin n → ℝ) (t : ℝ) :
    Tendsto (fun s => P.continuationValue (pendingClockSet s u) (max 0 (1-s)) 1 z)
      (𝓝[>] t) (𝓝 (P.continuationValue (strictPendingClockSet t u) (max 0 (1-t)) 1 z)) := by
  let A := strictPendingClockSet t u
  have hA := P.restrictTo_integrable_maximum A hP
  have hV := Model.optimalScalarValue_durationWeight_continuousOn (P.restrictTo A) hA (by norm_num : (0 : ℝ) ≤ 1)
  have hcoef : Continuous (fun s : ℝ => z * max 0 (1-s)) :=
    continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id))
  have hg : Continuous (fun s : ℝ => P.continuationValue A (max 0 (1-s)) 1 z) :=
    hV.comp_continuous hcoef (fun s => mul_nonneg hz (le_max_left _ _))
  apply (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  exact (pendingClockSet_eventually_eq_right u t).mono fun s hs =>
    congrArg (fun B => P.continuationValue B (max 0 (1-s)) 1 z) hs.symm

end ProphetSecretary.Probability
