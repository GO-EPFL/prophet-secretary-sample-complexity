import ProphetSecretary.Model.Instance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Reflection of an independent uniform clock

Changing elapsed fraction `t` to remaining fraction `1-t` preserves the
uniform law. The identity is used only to rewrite analytical expectations.
-/

open MeasureTheory Set

namespace ProphetSecretary.Probability

lemma integral_uniformClock_reflection (f : ℝ → ℝ) :
    (∫ t, f (1-t) ∂Model.Instance.uniformClock) =
      ∫ s, f s ∂Model.Instance.uniformClock := by
  unfold Model.Instance.uniformClock
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left]
  simp

lemma uniformClock_reflection_measurePreserving :
    MeasurePreserving (fun t : ℝ => 1-t) Model.Instance.uniformClock Model.Instance.uniformClock := by
  have hm : Measurable (fun t : ℝ => 1-t) := by fun_prop
  refine ⟨hm, ?_⟩
  haveI : IsProbabilityMeasure (Model.Instance.uniformClock.map (fun t : ℝ => 1-t)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_Iic
  intro s
  have hpre : MeasurableSet {t : ℝ | 1-t ≤ s} := measurableSet_le hm measurable_const
  have h := integral_uniformClock_reflection (fun t : ℝ => if t ≤ s then 1 else 0)
  have hleft : (∫ t : ℝ, (if 1-t ≤ s then (1 : ℝ) else 0) ∂Model.Instance.uniformClock) =
      Model.Instance.uniformClock.real {t : ℝ | 1-t ≤ s} := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := Model.Instance.uniformClock) (1 : ℝ) hpre
  have hright : (∫ t : ℝ, (if t ≤ s then (1 : ℝ) else 0) ∂Model.Instance.uniformClock) =
      Model.Instance.uniformClock.real (Iic s) := by
    simpa only [Set.indicator_apply, Set.mem_Iic, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := Model.Instance.uniformClock) (1 : ℝ) measurableSet_Iic
  rw [hleft, hright] at h
  have hmap : (Model.Instance.uniformClock.map (fun t : ℝ => 1-t)).real (Iic s) =
      Model.Instance.uniformClock.real (Iic s) := by
    rw [map_measureReal_apply hm measurableSet_Iic]
    exact h
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans
    ((congrArg ENNReal.ofReal hmap).trans (ENNReal.ofReal_toReal (measure_ne_top _ _)))

lemma clocks_reflection_measurePreserving (n : ℕ) :
    MeasurePreserving (fun u : Fin n → ℝ => fun i => 1-u i)
      (Model.Instance.clocksLaw n) (Model.Instance.clocksLaw n) :=
  measurePreserving_pi _ _ (fun _ => uniformClock_reflection_measurePreserving)

end ProphetSecretary.Probability
