import ProphetSecretary.Statistics.GridEntranceStateLimit

/-!
# Measurable post-arrival size at the true entrance

The strict unseen set keeps track of every identity, including observed zeros.
Its joint time/clock measurability and the measurable true entrance give the
actual size multiplier used in the limiting weighted moment estimate.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma measurable_strictPendingClockSet_joint : Measurable
    (fun q : ℝ × (Fin n → ℝ) => strictPendingClockSet q.1 q.2) := by
  rw [measurable_finset_iff]
  intro i
  apply measurableSet_setOf.mp
  have hu : Measurable (fun q : ℝ × (Fin n → ℝ) => q.2 i) :=
    (measurable_pi_apply i : Measurable (fun u : Fin n → ℝ => u i)).comp measurable_snd
  have hset : MeasurableSet {q : ℝ × (Fin n → ℝ) | q.1 < q.2 i} := measurableSet_lt measurable_fst hu
  simpa only [Set.preimage_setOf_eq,mem_strictPendingClockSet] using hset

end ProphetSecretary.Probability

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.measurable_postRemainingSize_joint (P : Instance n) : Measurable
    (fun q : ℝ × (Fin n → ℝ) => P.postRemainingSize q.1 q.2) := by
  have hmask := ProphetSecretary.Probability.measurable_strictPendingClockSet_joint (n := n)
  have hmean : Measurable (fun q : ℝ × (Fin n → ℝ) =>
      (P.restrictTo (ProphetSecretary.Probability.strictPendingClockSet q.1 q.2)).totalFirstMoment) :=
    (measurable_of_finite (fun A : Finset (Fin n) => (P.restrictTo A).totalFirstMoment)).comp hmask
  have htime : Measurable (fun q : ℝ × (Fin n → ℝ) => 1-q.1) := measurable_const.sub measurable_fst
  exact hmean.add htime

lemma Instance.measurable_trueEntrance_postSize (P : Instance n) (hi a : ℝ) : Measurable
    (fun u : Fin n → ℝ => P.postRemainingSize (P.trueCriticalEntrance hi a u) u) := by
  have hpair : Measurable (fun u : Fin n → ℝ => (P.trueCriticalEntrance hi a u,u)) :=
    (P.measurable_trueCriticalEntrance hi a).prodMk measurable_id
  change Measurable ((fun q : ℝ × (Fin n → ℝ) => P.postRemainingSize q.1 q.2) ∘
    (fun u : Fin n → ℝ => (P.trueCriticalEntrance hi a u,u)))
  exact P.measurable_postRemainingSize_joint.comp hpair

end ProphetSecretary.Model
