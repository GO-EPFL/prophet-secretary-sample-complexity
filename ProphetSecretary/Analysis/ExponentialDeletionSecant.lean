import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# An exponential secant bound for deleting finite Poisson intensity

The constant depends only on the finite mass bound `L`. Zero tail mass is
allowed. This compares a full deletion with a positive intensity secant and
is used before taking the derivative limit in the benchmark calculation.
-/
namespace ProphetSecretary.Analysis

theorem exponential_deletion_secant {z L h : ℝ}
    (hz : 0 ≤ z) (hzL : z ≤ L) (hh : 0 < h) (hh1 : h ≤ 1) :
    h*(1-Real.exp (-z)) ≤ Real.exp (2*L)*(Real.exp (-z)-Real.exp (-(1+h)*z)) := by
  have hUpper : 1-Real.exp (-z) ≤ z := by linarith only [Real.add_one_le_exp (-z)]
  have hu : 0 ≤ h*z := mul_nonneg hh.le hz
  have hLower : h*z ≤ Real.exp (h*z)-1 := by linarith only [Real.add_one_le_exp (h*z)]
  have hPositive : 0 ≤ Real.exp (h*z)-1 := hu.trans hLower
  have hExponent : 0 ≤ 2*L-(1+h)*z := by
    have hProduct := mul_le_mul_of_nonneg_right hh1 hz
    nlinarith only [hzL,hProduct]
  have hFactor : 1 ≤ Real.exp (2*L-(1+h)*z) := Real.one_le_exp_iff.mpr hExponent
  have hIdentity : Real.exp (2*L-(1+h)*z)*(Real.exp (h*z)-1)=
      Real.exp (2*L)*(Real.exp (-z)-Real.exp (-(1+h)*z)) := by
    rw [mul_sub,mul_sub,mul_one,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  calc
    _ ≤ h*z := mul_le_mul_of_nonneg_left hUpper hh.le
    _ ≤ Real.exp (h*z)-1 := hLower
    _ ≤ Real.exp (2*L-(1+h)*z)*(Real.exp (h*z)-1) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hFactor hPositive
    _ = _ := hIdentity

end ProphetSecretary.Analysis
