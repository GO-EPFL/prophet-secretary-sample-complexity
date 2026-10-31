import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Real

/-!
# A nonnegative probability law is determined by its nonnegative upper tails

The positive part determines the mass at zero because the total mass is one.
This retains zero observations when identifying zero-inflated likelihood laws.
-/
open MeasureTheory Set
namespace ProphetSecretary.Probability

lemma measure_eq_of_nonnegative_real_upper_tails (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0≤x) (hν : ∀ᵐ x ∂ν, 0≤x)
    (hTail : ∀ x : ℝ, 0≤x → μ.real (Ioi x)=ν.real (Ioi x)) : μ=ν := by
  apply Measure.ext_of_Iic
  intro x
  by_cases hx : 0≤x
  · have hT : μ (Ioi x)=ν (Ioi x) := by
      calc
        _ = ENNReal.ofReal (μ.real (Ioi x)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ = ENNReal.ofReal (ν.real (Ioi x)) := congrArg ENNReal.ofReal (hTail x hx)
        _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
    have hCμ : μ (Iic x)=1-μ (Ioi x) := by
      simpa only [compl_Ioi,measure_univ] using (measure_compl (μ := μ) (s := Ioi x) measurableSet_Ioi (measure_ne_top _ _))
    have hCν : ν (Iic x)=1-ν (Ioi x) := by
      simpa only [compl_Ioi,measure_univ] using (measure_compl (μ := ν) (s := Ioi x) measurableSet_Ioi (measure_ne_top _ _))
    rw [hCμ,hCν,hT]
  · have hNeg : x<0 := lt_of_not_ge hx
    have hNullμ : μ (Iic x)=0 := measure_eq_zero_iff_ae_notMem.mpr
      (hμ.mono (fun y hy hle => not_lt_of_ge hy (hle.trans_lt hNeg)))
    have hNullν : ν (Iic x)=0 := measure_eq_zero_iff_ae_notMem.mpr
      (hν.mono (fun y hy hle => not_lt_of_ge hy (hle.trans_lt hNeg)))
    exact hNullμ.trans hNullν.symm
end ProphetSecretary.Probability
