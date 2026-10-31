import ProphetSecretary.Statistics.RemainingSize
import ProphetSecretary.Probability.PendingStateRightLimit

/-!
# Stabilization of unseen identities at a decreasing-time limit

Times approaching an entrance from above need not be monotone. If none of the
grid times equals an arrival, the finite pending set eventually equals the
actual post-arrival entrance state. Remaining first moment and horizon then
converge together. Grid/arrival non-equality is a separate no-atom obligation.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Probability

variable {n : ℕ}

theorem pendingClockSet_stabilizes_at_limit (u : Fin n → ℝ) {σ : ℝ} {s : ℕ → ℝ}
    (hlim : Tendsto s atTop (𝓝 σ)) (hLower : ∀ m, σ≤s m) (hNoTie : ∀ m i, s m ≠ u i) :
    ∀ᶠ m in atTop, pendingClockSet (s m) u = strictPendingClockSet σ u := by
  have hall : ∀ᶠ m in atTop, ∀ i, s m ≤ u i ↔ σ < u i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : σ < u i
    · have hh : ∀ᶠ m in atTop, s m < u i := hlim.eventually (isOpen_Iio.mem_nhds hi)
      exact hh.mono fun m hm => ⟨fun _ => hi,fun _ => hm.le⟩
    · exact Eventually.of_forall fun m => by
        have hle : u i ≤ s m := (le_of_not_gt hi).trans (hLower m)
        have hlt : u i < s m := lt_of_le_of_ne hle (Ne.symm (hNoTie m i))
        simp only [not_le.mpr hlt,hi]
  exact hall.mono fun m hm => Finset.ext fun i => by
    rw [mem_pendingClockSet,mem_strictPendingClockSet]
    exact hm i

end ProphetSecretary.Probability

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.postRemainingSize (P : Instance n) (t : ℝ) (u : Fin n → ℝ) : ℝ :=
  (P.restrictTo (ProphetSecretary.Probability.strictPendingClockSet t u)).totalFirstMoment + (1-t)

lemma Instance.postRemainingSize_mem (P : Instance n) {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) (u : Fin n → ℝ) :
    P.postRemainingSize t u ∈ Icc (0 : ℝ) (P.totalFirstMoment+1) := by
  constructor
  · exact add_nonneg (P.restrictTo _).totalFirstMoment_nonnegative (sub_nonneg.mpr ht1)
  · have h := P.totalFirstMoment_restrictTo_le (ProphetSecretary.Probability.strictPendingClockSet t u)
    unfold postRemainingSize
    linarith only [h,ht0]

theorem Instance.remainingSize_tendsto_post (P : Instance n) (u : Fin n → ℝ) {σ : ℝ} {s : ℕ → ℝ}
    (hlim : Tendsto s atTop (𝓝 σ)) (hLower : ∀ m, σ≤s m) (hNoTie : ∀ m i, s m ≠ u i) :
    Tendsto (fun m => P.remainingSize (s m) u) atTop (𝓝 (P.postRemainingSize σ u)) := by
  have hsets := ProphetSecretary.Probability.pendingClockSet_stabilizes_at_limit u hlim hLower hNoTie
  have hbase : Tendsto (fun m =>
      (P.restrictTo (ProphetSecretary.Probability.strictPendingClockSet σ u)).totalFirstMoment + (1-s m))
      atTop (𝓝 (P.postRemainingSize σ u)) := tendsto_const_nhds.add (tendsto_const_nhds.sub hlim)
  apply hbase.congr'
  exact hsets.mono fun m hm => by
    change (P.restrictTo (ProphetSecretary.Probability.strictPendingClockSet σ u)).totalFirstMoment + (1-s m) =
      (P.restrictTo (ProphetSecretary.Probability.pendingClockSet (s m) u)).totalFirstMoment + (1-s m)
    rw [hm]

end ProphetSecretary.Model
