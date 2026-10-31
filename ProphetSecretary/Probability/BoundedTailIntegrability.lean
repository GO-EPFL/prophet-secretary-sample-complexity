import ProphetSecretary.Probability.BoundedCDFMean
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrability of the strict tail of a bounded random variable

The strict tail vanishes above the actual almost-sure upper bound. This
justifies the half-line integrals used to average pilot probability estimates.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma measurable_real_strict_tail (X : Ω → ℝ) : Measurable (fun t : ℝ => μ.real {ω | t < X ω}) := by
  have hAnti : Antitone (fun t : ℝ => μ {ω | t < X ω}) :=
    fun _ _ h => measure_mono (fun _ hx => lt_of_le_of_lt h hx)
  exact hAnti.measurable.ennreal_toReal

lemma real_strict_tail_le_one (X : Ω → ℝ) (t : ℝ) : μ.real {ω | t < X ω} ≤ 1 :=
  (measureReal_mono (subset_univ _)).trans_eq probReal_univ

lemma integrableOn_real_strict_tail_of_bounded {X : Ω → ℝ} {H : ℝ}
    (hBound : ∀ᵐ ω ∂μ, X ω ≤ H) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t < X ω}) (Ioi 0) := by
  let T := fun t : ℝ => μ.real {ω | t < X ω}
  have hMeas : Measurable T := measurable_real_strict_tail X
  have hI : IntegrableOn T (Ioc (0 : ℝ) H) := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable 1
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
      exact real_strict_tail_le_one X t
  have hIndicator : Integrable ((Ioc (0 : ℝ) H).indicator T) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hI
  have hZero (t : ℝ) (ht : H < t) : T t = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact hBound.mono fun ω hω => not_lt_of_ge (hω.trans ht.le)
  apply hIndicator.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases htH : t ≤ H
  · exact Set.indicator_of_mem (show t∈Ioc (0 : ℝ) H from ⟨ht,htH⟩) T
  · rw [Set.indicator_of_notMem (show t∉Ioc (0 : ℝ) H from fun h => htH h.2)]
    exact (hZero t (lt_of_not_ge htH)).symm

end ProphetSecretary.Probability
