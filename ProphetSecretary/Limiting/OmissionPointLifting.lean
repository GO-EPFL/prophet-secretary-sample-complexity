import ProphetSecretary.Limiting.OmissionObserverMatching

/-!
# Actual high-point correspondence on the omission coupling

Counting-measure equality transports an old anonymous point above the cutoff
to a point of the new finite configuration. This is an analytical occurrence
correspondence; no Poisson construction label is revealed to a policy.
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Limiting
open CountableInstance

lemma countingMeasure_singleton_ne_zero_iff (ω : Configuration) (p : Point) :
    countingMeasure ω {p} ≠ 0 ↔ ∃ j : Fin ω.1, ω.2 j=p := by
  constructor
  · intro h
    by_contra hn
    have hj : ∀ j : Fin ω.1, ω.2 j ≠ p := by simpa only [not_exists] using hn
    apply h
    change (∑ j : Fin ω.1, Measure.dirac (ω.2 j)) {p}=0
    rw [Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    simp [Measure.dirac_apply',hj j]
  · rintro ⟨j,hj⟩
    have hLe : Measure.dirac (ω.2 j) {p} ≤ countingMeasure ω {p} := by
      change _ ≤ (∑ k : Fin ω.1, Measure.dirac (ω.2 k)) {p}
      rw [Measure.finsetSum_apply]
      exact Finset.single_le_sum (f := fun k : Fin ω.1 => Measure.dirac (ω.2 k) {p})
        (fun _ _ => bot_le) (Finset.mem_univ j)
    have hOne : (1 : ℝ≥0∞) ≤ countingMeasure ω {p} := by simpa [hj] using hLe
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hOne)

lemma bandCountingMeasure_singleton_ne_zero (ω : BandConfigurations) (k : ℕ)
    (j : Fin (ω k).1) : bandCountingMeasure ω {(ω k).2 j} ≠ 0 := by
  have hCount : countingMeasure (ω k) {(ω k).2 j} ≠ 0 :=
    (countingMeasure_singleton_ne_zero_iff _ _).2 ⟨j,rfl⟩
  have hLe : countingMeasure (ω k) {(ω k).2 j} ≤ bandCountingMeasure ω {(ω k).2 j} := by
    rw [bandCountingMeasure,Measure.sum_apply _ (measurableSet_singleton ((ω k).2 j))]
    exact ENNReal.le_tsum k
  exact fun h => hCount (le_antisymm (h ▸ hLe) bot_le)

lemma omission_high_point_lift (B : CountableInstance) {Seed : Type*}
    (q : OmissionExecutionWorld Seed) {b : ℝ}
    (hCount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    (hLow : LowCloudRegular B b q.1.1.2)
    (hHigh : ∀ j : Fin q.1.1.1.1, b < (q.1.1.1.2 j).2)
    (k : ℕ) (j : Fin (q.1.2 k).1) (hj : b < ((q.1.2 k).2 j).2) :
    ∃ l : Fin q.1.1.1.1, q.1.1.1.2 l=(q.1.2 k).2 j := by
  apply (countingMeasure_singleton_ne_zero_iff q.1.1.1 ((q.1.2 k).2 j)).1
  rw [← omission_high_countingMeasure_eq B q hCount hLow hHigh,
    Measure.restrict_apply (measurableSet_singleton ((q.1.2 k).2 j))]
  have hSet : {(q.1.2 k).2 j} ∩ (univ ×ˢ Ioi b) = {(q.1.2 k).2 j} :=
    inter_eq_left.mpr (by intro p hp; rcases mem_singleton_iff.mp hp with rfl; exact ⟨mem_univ _,hj⟩)
  rw [hSet]
  exact bandCountingMeasure_singleton_ne_zero q.1.2 k j

end ProphetSecretary.Limiting
