import ProphetSecretary.Probability.CensoredContinuation

/-!
# Left limits of finite unseen-state values

Along each finite clock vector, the unseen identity set is constant sufficiently
close to an elapsed time from below. Scalar value is continuous in its remaining
duration weight. This includes remaining horizon zero; no assertion that a
nonempty reward-only continuation has value zero is made.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma pendingClockSet_eventually_eq_left (u : Fin n → ℝ) (t : ℝ) :
    ∀ᶠ s in 𝓝[<] t, pendingClockSet s u = pendingClockSet t u := by
  have hall : ∀ᶠ s in 𝓝[<] t, ∀ i, s ≤ u i ↔ t ≤ u i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : t ≤ u i
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with s hs
      exact ⟨fun _ => hi, fun _ => hs.le.trans hi⟩
    · have hlt : u i < t := lt_of_not_ge hi
      have hh : ∀ᶠ s in 𝓝 t, u i < s := isOpen_Ioi.mem_nhds hlt
      filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with s hs
      simp only [not_le.mpr hs, hi]
  exact hall.mono fun s hs => Finset.ext fun i => by
    rw [mem_pendingClockSet, mem_pendingClockSet]
    exact hs i

/-- A fixed finite instance has the required pathwise left-continuity even at
zero remaining horizon, because only the weight changes in the fixed state. -/
theorem pendingContinuationValue_tendsto_left (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z)
    (u : Fin n → ℝ) (t : ℝ) :
    Tendsto (fun s => P.continuationValue (pendingClockSet s u) (max 0 (1-s)) 1 z)
      (𝓝[<] t) (𝓝 (P.continuationValue (pendingClockSet t u) (max 0 (1-t)) 1 z)) := by
  let A := pendingClockSet t u
  have hA := P.restrictTo_integrable_maximum A hP
  have hV := Model.optimalScalarValue_durationWeight_continuousOn (P.restrictTo A) hA (by norm_num : (0 : ℝ) ≤ 1)
  have hcoef : Continuous (fun s : ℝ => z * max 0 (1-s)) :=
    continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id))
  have hg : Continuous (fun s : ℝ => P.continuationValue A (max 0 (1-s)) 1 z) :=
    hV.comp_continuous hcoef (fun s => mul_nonneg hz (le_max_left _ _))
  apply (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  exact (pendingClockSet_eventually_eq_left u t).mono fun s hs =>
    congrArg (fun B => P.continuationValue B (max 0 (1-s)) 1 z) hs.symm

end ProphetSecretary.Probability
