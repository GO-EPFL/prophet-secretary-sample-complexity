import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Real

/-!
# Constant selection and a location identity make the competing CDF constant

Let `a(x)=C*ν(-∞,x)` for almost every positive marginal value, with `C≠0`.
If `a` is marginally constant and `a(0)=0`, the strict CDF is marginally
constant as well. A zero atom forces that constant to be zero; without a zero
atom, positive values have full marginal measure. Nonnegativity of the
competing law supplies its strict CDF value at zero.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Probability

theorem strictCdf_ae_constant_of_constant_location
    (κ ν : Measure ℝ) [IsProbabilityMeasure κ] [IsFiniteMeasure ν]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hν : ∀ᵐ y ∂ν, 0 ≤ y)
    (C : ℝ) (hC : C≠0) (a : ℝ → ℝ) (ha0 : a 0=0)
    (p : ℝ) (ha : a =ᵐ[κ] fun _ => p)
    (hLocation : ∀ᵐ x ∂κ, 0<x → a x=C*ν.real (Iio x)) :
    ∃ k : ℝ, (fun x => ν.real (Iio x)) =ᵐ[κ] fun _ => k := by
  by_cases hAtom : κ ({0} : Set ℝ)=0
  · have hPositive : ∀ᵐ x ∂κ, 0<x := by
      filter_upwards [hκ,measure_eq_zero_iff_ae_notMem.mp hAtom] with x hx hNot
      have hNe : x≠0 := fun he => hNot (by simp only [he,mem_singleton_iff])
      exact lt_of_le_of_ne hx hNe.symm
    have hConstant : ∀ᵐ x ∂κ, C*ν.real (Iio x)=p := by
      filter_upwards [hPositive,ha,hLocation] with x hx hax hLoc
      exact (hLoc hx).symm.trans hax
    obtain ⟨x₀,hx₀⟩ := hConstant.exists
    refine ⟨ν.real (Iio x₀),?_⟩
    filter_upwards [hConstant] with x hx
    exact mul_left_cancel₀ hC (hx.trans hx₀.symm)
  · obtain ⟨x,hx,hax⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hAtom (ae_restrict_of_ae ha)
    have hx0 : x=0 := mem_singleton_iff.mp hx
    have hp : p=0 := by rw [hx0,ha0] at hax; exact hax.symm
    have hF0 : ν.real (Iio (0 : ℝ))=0 := by
      have hMass : ν (Iio (0 : ℝ))=0 := measure_eq_zero_iff_ae_notMem.mpr
        (hν.mono (fun _ hy => not_lt.mpr hy))
      rw [measureReal_def,hMass,ENNReal.toReal_zero]
    refine ⟨0,?_⟩
    filter_upwards [hκ,ha,hLocation] with y hy hay hLoc
    by_cases hy0 : 0<y
    · have h : C*ν.real (Iio y)=0 := (hLoc hy0).symm.trans (hay.trans hp)
      exact (mul_eq_zero.mp h).resolve_left hC
    · have hyEq : y=0 := le_antisymm (le_of_not_gt hy0) hy
      rw [hyEq,hF0]

end ProphetSecretary.Probability
