import ProphetSecretary.Analysis.ClassifierExponential
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit preliminary round count and classifier error

The observable classifier uses ceil(64 log m) rounds. Both source exponential
bounds are at most m^(-4), with no dependence on the number of marginals.
-/

open Set
namespace ProphetSecretary.Analysis

noncomputable def classifierRounds (m : ℕ) : ℕ := ⌈64*Real.log (m:ℝ)⌉₊

lemma classifierRounds_lower (m : ℕ) : 64*Real.log (m:ℝ)≤classifierRounds m := Nat.le_ceil _

lemma classifierRounds_upper {m : ℕ} (hm : 1≤m) :
    (classifierRounds m:ℝ)<64*Real.log (m:ℝ)+1 :=
  Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hm)))

lemma classifierRounds_positive {m : ℕ} (hm : 2≤m) : 0<classifierRounds m := by
  apply Nat.one_le_ceil_iff.mpr
  have hm' : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
  exact mul_pos (by norm_num) (Real.log_pos hm')

private lemma exp_neg_four_log {m : ℕ} (hm : 0<m) :
    Real.exp (-4*Real.log (m:ℝ))=1/(m:ℝ)^4 := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  rw [show -4*Real.log (m:ℝ)= -(4*Real.log (m:ℝ)) by ring,Real.exp_neg]
  rw [show (4:ℝ)=(4:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hm',one_div]

lemma classifier_lower_error_le_inverse_fourth {m : ℕ} (hm : 1≤m) {S : ℝ} (hS : 1≤S) :
    Real.exp (-(classifierRounds m:ℝ)*S/6)≤1/(m:ℝ)^4 := by
  have hH := classifierRounds_lower m
  have hLog := Real.log_nonneg (show (1:ℝ)≤m by exact_mod_cast hm)
  have hProd := le_mul_of_one_le_right (Nat.cast_nonneg (classifierRounds m)) hS
  rw [←exp_neg_four_log (show 0<m by omega)]
  apply Real.exp_le_exp.mpr
  nlinarith only [hH,hLog,hProd]

lemma classifier_upper_error_le_inverse_fourth {m : ℕ} (hm : 1≤m) {S : ℝ} (hS : 1≤S) :
    Real.exp (-3*(classifierRounds m:ℝ)*S/8)≤1/(m:ℝ)^4 := by
  apply le_trans (b:=Real.exp (-(classifierRounds m:ℝ)*S/6))
  · apply Real.exp_le_exp.mpr
    have hProd := mul_nonneg (Nat.cast_nonneg (classifierRounds m)) (show 0≤S by linarith only [hS])
    linarith only [hProd]
  · exact classifier_lower_error_le_inverse_fourth hm hS

/-- An explicit instance-size-independent threshold for the final hard budget. -/
lemma classifierRounds_le_rounds {m : ℕ} (hm : 65536≤m) : classifierRounds m≤m := by
  have hm1 : 1≤m := by omega
  have hSq : (Real.sqrt (m:ℝ))^2=(m:ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
  have hRoot : (256:ℝ)≤Real.sqrt (m:ℝ) := Real.le_sqrt_of_sq_le (by norm_num;exact hm)
  have hLog := Real.log_le_rpow_div (Nat.cast_nonneg m) (show (0:ℝ)<1/2 by norm_num)
  rw [←Real.sqrt_eq_rpow] at hLog
  have hCeil := classifierRounds_upper hm1
  have hProd := mul_nonneg (Real.sqrt_nonneg (m:ℝ)) (sub_nonneg.mpr hRoot)
  have hBound : (classifierRounds m:ℝ)≤m := by nlinarith only [hSq,hRoot,hLog,hCeil,hProd]
  exact_mod_cast hBound

lemma classifier_hard_budget_le_four_rounds {m : ℕ} (hm : 65536≤m) :
    classifierRounds m+3*m≤4*m := by
  have h := classifierRounds_le_rounds hm
  omega

end ProphetSecretary.Analysis
