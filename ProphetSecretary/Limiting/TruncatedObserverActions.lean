import ProphetSecretary.Limiting.AcceptedPointMeasure
import ProphetSecretary.Limiting.CountableTruncatedRule

/-!
# Actual actions of the embedded truncated observer

A finite high-mark counting measure is supplied only as analytical input to the
payoff functional. Each callback receives its strict past restriction. These
identities include retained zero-valued observations and all anonymous past
points above the cutoff.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {N : ℕ} {Seed : Type*}

noncomputable def truncatedObserverWorld (μ : FiniteMeasure Point) (v : CompleteWorld Seed) :
    FiniteObserverWorld N Seed :=
  (μ,((fun i : Fin N => v.2.1 i.val),((fun i : Fin N => v.2.2.1 i.val),v.2.2.2)))

lemma filtered_past_eq_finitePast (ω : BandConfigurations) (μ : FiniteMeasure Point) (b : ℝ)
    (hμ : (μ : Measure Point) = (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)) (t : ℝ) :
    (anonymousHistory ω t).restrict (univ ×ˢ Ioi b) = finitePast μ t := by
  rw [anonymousHistory_markRestriction,← hμ]
  rfl

lemma extended_individual_action (π : HybridRule N Seed) (b : ℝ)
    (v : CompleteWorld Seed) (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b))
    (j : ℕ) (hj : j < N) :
    (extendTruncatedRule π b).candidateAction v (Sum.inl j) =
      π.individualMeasureAction (truncatedObserverWorld μ v) ⟨j,hj⟩ := by
  simp only [CountableRule.candidateAction,candidatePoint,extendTruncatedRule,dif_pos hj]
  rw [prefixHistory_actual,filtered_past_eq_finitePast v.1 μ b hμ]
  rfl

lemma extended_anonymous_action (π : HybridRule N Seed) (b : ℝ)
    (v : CompleteWorld Seed) (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b))
    (k j : ℕ) :
    (extendTruncatedRule π b).candidateAction v (Sum.inr (k,j)) =
      if b < (configurationPoint j (v.1 k)).2 then
        π.anonymousMeasureAction (truncatedObserverWorld μ v) (configurationPoint j (v.1 k)) else false := by
  simp only [CountableRule.candidateAction,candidatePoint,extendTruncatedRule]
  rw [prefixHistory_actual,filtered_past_eq_finitePast v.1 μ b hμ]
  rfl

lemma extended_individual_accepted_iff (π : HybridRule N Seed) (b : ℝ)
    (v : CompleteWorld Seed) (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b))
    (j : ℕ) (hj : j < N) :
    (extendTruncatedRule π b).codeAccepted v (candidateEnumeration (Sum.inl j)) ↔
      π.individualMeasureAccepted (truncatedObserverWorld μ v) ⟨j,hj⟩ := by
  simp only [CountableRule.codeAccepted,codePresent,codeTime,codePoint,
    Equiv.symm_apply_apply,candidatePresent,candidatePoint,true_and]
  rw [extended_individual_action π b v μ hμ j hj]
  rfl

lemma extended_individual_notAccepted (π : HybridRule N Seed) (b : ℝ)
    (v : CompleteWorld Seed) (j : ℕ) (hj : ¬j < N) :
    ¬(extendTruncatedRule π b).codeAccepted v (candidateEnumeration (Sum.inl j)) := by
  simp only [CountableRule.codeAccepted,codePresent,codeTime,codePoint,
    Equiv.symm_apply_apply,candidatePresent,candidatePoint,true_and,
    CountableRule.candidateAction,extendTruncatedRule,dif_neg hj]
  simp

lemma extended_anonymous_accepted_iff (π : HybridRule N Seed) (b : ℝ)
    (v : CompleteWorld Seed) (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b))
    (k : ℕ) (j : Fin (v.1 k).1) :
    (extendTruncatedRule π b).codeAccepted v (candidateEnumeration (Sum.inr (k,j.val))) ↔
      b < ((v.1 k).2 j).2 ∧ π.anonymousMeasureAccepted (truncatedObserverWorld μ v) ((v.1 k).2 j) := by
  simp only [CountableRule.codeAccepted,codePresent,codeTime,codePoint,
    Equiv.symm_apply_apply,candidatePresent,candidatePoint]
  rw [extended_anonymous_action π b v μ hμ k j.val]
  simp only [configurationPoint,j.isLt,true_and]
  by_cases hx : b < ((v.1 k).2 j).2
  · simp [hx,HybridRule.anonymousMeasureAccepted]
  · simp [hx]

end ProphetSecretary.Limiting.CountableInstance
