import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit loss constant in the outer reduction

The local lift loses K M_ret/m and at most (K+rho)H/m. The pilot scale
H≤10^6 M gives a constant independent of the number of variables.
-/

namespace ProphetSecretary.Analysis

def outerReductionLocalConstant (K : ℝ) : ℝ := 1000001*K+1000000

lemma outerReductionLocalConstant_nonneg {K : ℝ} (hK : 0≤K) : 0≤outerReductionLocalConstant K := by
  unfold outerReductionLocalConstant
  positivity

lemma outer_reduction_local_loss {C K Mret M H R : ℝ} {m : ℕ}
    (hm : 0<m) (hK : 0≤K) (hC : C≤1) (hMean : Mret≤M) (hH : 0≤H) (hScale : H≤1000000*M)
    (hGain : (C-K/(m:ℝ))*Mret-H*(K/(m:ℝ))-(C-K/(m:ℝ))*(H/(m:ℝ))≤R) :
    C*Mret-outerReductionLocalConstant K*M/(m:ℝ)≤R := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hρ : C-K/(m:ℝ)≤1 := (sub_le_self C (div_nonneg hK hmR.le)).trans hC
  have hFirst := mul_le_mul_of_nonneg_left hMean hK
  have hSecond := mul_le_mul (add_le_add (le_refl K) hρ) hScale hH (by linarith : 0≤K+1)
  have hLoss : K*Mret+(K+(C-K/(m:ℝ)))*H≤outerReductionLocalConstant K*M := by
    unfold outerReductionLocalConstant
    nlinarith only [hFirst,hSecond]
  have hMul := mul_le_mul_of_nonneg_right hGain hmR.le
  have hExpr : ((C-K/(m:ℝ))*Mret-H*(K/(m:ℝ))-(C-K/(m:ℝ))*(H/(m:ℝ)))*(m:ℝ)=
      C*Mret*(m:ℝ)-K*Mret-(K+(C-K/(m:ℝ)))*H := by
    field_simp [ne_of_gt hmR]
    ring
  rw [hExpr] at hMul
  apply (sub_le_iff_le_add).mpr
  apply (mul_le_mul_iff_left₀ hmR).mp
  have hRight : (R+outerReductionLocalConstant K*M/(m:ℝ))*(m:ℝ)=R*(m:ℝ)+outerReductionLocalConstant K*M := by
    field_simp [ne_of_gt hmR]
  rw [hRight]
  linarith only [hMul,hLoss]

end ProphetSecretary.Analysis
