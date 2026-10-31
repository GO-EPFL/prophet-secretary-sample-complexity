import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Explicit exponential estimates for the observable first-moment classifier

The constants give the paper's upper-tail exponent 3/8 at t=2/3 and lower-tail
exponent 1/6 at t=-1/3. The numerical estimates use a finite Taylor remainder.
-/

open Finset Set
namespace ProphetSecretary.Analysis

lemma exp_two_thirds_le : Real.exp (2/3 : ℝ)≤47/24 := by
  have h := Real.exp_bound (x:=(2/3 : ℝ)) (by norm_num) (n:=5) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith [(abs_le.mp h).2]

lemma exp_neg_third_le : Real.exp (-1/3 : ℝ)≤13/18 := by
  have h := Real.exp_bound (x:=(-1/3 : ℝ)) (by norm_num) (n:=4) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith [(abs_le.mp h).2]

lemma exp_mul_unit_chord (t x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    Real.exp (t*x)≤1+x*(Real.exp t-1) := by
  have h := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ t)
    (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel 1 x)
  simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at h
  rw [mul_comm x t] at h
  nlinarith only [h]

end ProphetSecretary.Analysis
