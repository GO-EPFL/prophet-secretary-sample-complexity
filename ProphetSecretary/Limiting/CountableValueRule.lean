import ProphetSecretary.Limiting.CountableContinuationContinuity
import ProphetSecretary.Limiting.CountableHistoryMask
import ProphetSecretary.Limiting.HybridValueThreshold

/-!
# A measurable countable Markov rule from actual continuation values

An individual candidate is removed from the unseen mask before evaluating its
continuation; an anonymous candidate leaves that mask unchanged. The rule uses
only the current value, elapsed time and observed identities, including zeros.
Positive acceptance ties are included. Optimality is a separate theorem.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def valueRule (B : CountableInstance) (w c : ℝ) : CountableRule Unit where
  individual _ t i x H _ := decide (0 < x ∧
    B.continuationValue (eraseMask (unseenMask H) i) w c (remainingTime t) ≤ w*x)
  poisson _ t x H _ := decide (0 < x ∧
    B.continuationValue (unseenMask H) w c (remainingTime t) ≤ w*x)

lemma valueRule_isMeasurable (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.valueRule w c).IsMeasurable := by
  constructor
  · let Ω := Unit × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point))))
    have ht : Measurable (fun z : Ω => z.2.1) := by fun_prop
    have hi : Measurable (fun z : Ω => z.2.2.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.2.2.1) := by fun_prop
    have hH : Measurable (fun z : Ω => z.2.2.2.2.1) := by fun_prop
    have hMask := measurable_eraseMask.comp ((measurable_unseenMask.comp hH).prodMk hi)
    have hU := continuous_remainingTime.measurable.comp ht
    have hV := (B.measurable_continuationValue hw hc).comp (hMask.prodMk hU)
    apply measurable_to_bool
    change MeasurableSet {z : Ω | decide (0 < z.2.2.2.1 ∧
      B.continuationValue (eraseMask (unseenMask z.2.2.2.2.1) z.2.2.1) w c
        (remainingTime z.2.1) ≤ w*z.2.2.2.1) = true}
    simp only [decide_eq_true_eq]
    exact (measurableSet_lt measurable_const hx).inter (measurableSet_le hV (hx.const_mul w))
  · let Ω := Unit × (Point × (IndividualHistory × Measure Point))
    have ht : Measurable (fun z : Ω => z.2.1.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.1.2) := by fun_prop
    have hH : Measurable (fun z : Ω => z.2.2.1) := by fun_prop
    have hMask := measurable_unseenMask.comp hH
    have hU := continuous_remainingTime.measurable.comp ht
    have hV := (B.measurable_continuationValue hw hc).comp (hMask.prodMk hU)
    apply measurable_to_bool
    change MeasurableSet {z : Ω | decide (0 < z.2.1.2 ∧
      B.continuationValue (unseenMask z.2.2.1) w c (remainingTime z.2.1.1) ≤ w*z.2.1.2) = true}
    simp only [decide_eq_true_eq]
    exact (measurableSet_lt measurable_const hx).inter (measurableSet_le hV (hx.const_mul w))

lemma valueRule_individual_positive (B : CountableInstance) (w c : ℝ) (t : ℝ) (i : ℕ) (x : ℝ)
    (H : IndividualHistory) (M : Measure Point)
    (h : (B.valueRule w c).individual () t i x H M = true) : 0 < x :=
  (of_decide_eq_true h).1

lemma valueRule_poisson_positive (B : CountableInstance) (w c : ℝ) (t x : ℝ)
    (H : IndividualHistory) (M : Measure Point)
    (h : (B.valueRule w c).poisson () t x H M = true) : 0 < x :=
  (of_decide_eq_true h).1

end ProphetSecretary.Limiting.CountableInstance
