import ProphetSecretary.Probability.WeightedClockVariance
import ProphetSecretary.Limiting.Compensator

/-!
# Fluctuations of the unseen finite-offer intensity

At elapsed time `t`, every still-unseen uniform clock has conditional rate
`1/(1-t)`. The expected absolute discrepancy of its weighted tail mass is
controlled by the square sum of the weights, uniformly in the instance size.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

noncomputable def tailHazardError (a : Fin N → ℝ) (t : ℝ) (u : Fin N → ℝ) : ℝ :=
  (∑ i, if t < u i then a i else 0) / (1 - t) - ∑ i, a i

lemma tailHazardError_eq_centered (a : Fin N → ℝ) {t : ℝ} (ht : t < 1) (u : Fin N → ℝ) :
    tailHazardError a t u =
      -(∑ i, a i * Probability.centeredIndicator (Iic t) t (u i)) / (1 - t) := by
  have hne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hsum : (∑ i, if t < u i then a i else 0) =
      (∑ i, a i) - ∑ i, a i * (if u i ≤ t then 1 else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i ≤ t
    · simp [hi, not_lt.mpr hi]
    · simp [hi, lt_of_not_ge hi]
  unfold tailHazardError Probability.centeredIndicator
  rw [hsum]
  simp only [Set.mem_Iic, mul_sub, Finset.sum_sub_distrib]
  field_simp
  rw [← Finset.mul_sum]
  ring

lemma tailHazardError_absoluteMean_le (a : Fin N → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ u, |tailHazardError a t u| ∂Model.Instance.clocksLaw N) ≤
      Real.sqrt (t / (1 - t)) * Real.sqrt (∑ i, (a i) ^ 2) := by
  have hh : 0 < 1 - t := sub_pos.mpr ht1
  have hprob : Model.Instance.uniformClock.real (Iic t) = t := by
    rw [measureReal_def, uniformClock_Iic ⟨ht0, ht1.le⟩, ENNReal.toReal_ofReal ht0]
  have hj := Probability.weighted_centeredIndicator_absoluteMean Model.Instance.uniformClock (A := Iic t) measurableSet_Iic a
  rw [hprob] at hj
  have habs (u : Fin N → ℝ) : |tailHazardError a t u| =
      |∑ i, a i * Probability.centeredIndicator (Iic t) t (u i)| / (1 - t) := by
    rw [tailHazardError_eq_centered a ht1 u, abs_div, abs_neg, abs_of_pos hh]
  calc
    _ = (∫ u, |∑ i, a i * Probability.centeredIndicator (Iic t) t (u i)|
        ∂Model.Instance.clocksLaw N) / (1 - t) := by
      simp_rw [habs]
      exact integral_div _ _
    _ ≤ Real.sqrt (t * (1 - t) * ∑ i, (a i) ^ 2) / (1 - t) := div_le_div_of_nonneg_right hj hh.le
    _ = _ := by
      rw [mul_assoc, Real.sqrt_mul ht0, Real.sqrt_mul hh.le, Real.sqrt_div ht0]
      calc
        _ = Real.sqrt t * Real.sqrt (∑ i, (a i) ^ 2) * (Real.sqrt (1 - t) / (1 - t)) := by ring
        _ = _ := by rw [Real.sqrt_div_self']; ring

end ProphetSecretary.Limiting
