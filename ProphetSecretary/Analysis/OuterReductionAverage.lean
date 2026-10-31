import ProphetSecretary.Analysis.OuterReductionLoss
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

/-!
# Averaging the explicit outer reduction loss

A good-event deficit D M/m and failure probability 2/m cost at most
(D+2C)M/m. The cutoff's retained mean loses at most one further C M/m.
All constants are explicit before any asymptotic notation.
-/

open MeasureTheory Set
namespace ProphetSecretary.Analysis

lemma outer_reduction_average {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 1≤m) {C D M : ℝ} (hC : 0≤C) (hD : 0≤D) (hM : 0≤M)
    {G : Set Ω} (hG : MeasurableSet G) (hFailure : μ.real Gᶜ≤2/(m:ℝ))
    {ret reward : Ω → ℝ} (hRetInt : Integrable ret μ) (hRewardInt : Integrable reward μ)
    (hRet : ∀ ω, ret ω≤M) (hReward : ∀ ω, 0≤reward ω)
    (hGood : ∀ ω∈G, C*ret ω-D*M/(m:ℝ)≤reward ω)
    (hMean : ((m:ℝ)/((m:ℝ)+1))*M≤∫ ω, ret ω ∂μ) :
    (C-(D+3*C)/(m:ℝ))*M≤∫ ω, reward ω ∂μ := by
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  let W : Ω → ℝ := Gᶜ.indicator (fun _ => 1)
  have hWI : Integrable W μ := (integrable_const 1).indicator hG.compl
  have hWMean : (∫ ω, W ω ∂μ)=μ.real Gᶜ := by
    simpa only [smul_eq_mul,mul_one] using integral_indicator_const (μ:=μ) (1:ℝ) hG.compl
  have hPoint (ω : Ω) : C*ret ω-D*M/(m:ℝ)-C*M*W ω≤reward ω := by
    by_cases hω : ω∈G
    · have hW : W ω=0 := Set.indicator_of_notMem (by simpa only [Set.mem_compl_iff,not_not] using hω) _
      rw [hW,mul_zero,sub_zero]
      exact hGood ω hω
    · have hW : W ω=1 := Set.indicator_of_mem (show ω∈Gᶜ from hω) _
      have hRetMul := mul_le_mul_of_nonneg_left (hRet ω) hC
      have hDloss : 0≤D*M/(m:ℝ) := div_nonneg (mul_nonneg hD hM) hmR.le
      rw [hW,mul_one]
      linarith only [hRetMul,hDloss,hReward ω]
  have hLowerInt := ((hRetInt.const_mul C).sub (integrable_const (D*M/(m:ℝ)))).sub (hWI.const_mul (C*M))
  have hInt := integral_mono hLowerInt hRewardInt hPoint
  change (∫ ω, C*ret ω-D*M/(m:ℝ)-C*M*W ω ∂μ)≤∫ ω, reward ω ∂μ at hInt
  rw [integral_sub (f:=fun ω => C*ret ω-D*M/(m:ℝ)) (g:=fun ω => C*M*W ω)
      ((hRetInt.const_mul C).sub (integrable_const (D*M/(m:ℝ)))) (hWI.const_mul (C*M)),
    integral_sub (f:=fun ω => C*ret ω) (g:=fun _ => D*M/(m:ℝ))
      (hRetInt.const_mul C) (integrable_const (D*M/(m:ℝ))),
    integral_const_mul,integral_const_mul,hWMean] at hInt
  simp only [integral_const,probReal_univ,one_smul] at hInt
  have hMeanMul := mul_le_mul_of_nonneg_left hMean hC
  have hFailureMul := mul_le_mul_of_nonneg_left hFailure (mul_nonneg hC hM)
  have hBound : C*((m:ℝ)/((m:ℝ)+1))*M-D*M/(m:ℝ)-C*M*(2/(m:ℝ))≤∫ ω, reward ω ∂μ := by
    linarith only [hInt,hMeanMul,hFailureMul]
  have hInv : 1/((m:ℝ)+1)≤1/(m:ℝ) := one_div_le_one_div_of_le hmR (by linarith)
  have hEq : (m:ℝ)/((m:ℝ)+1)=1-1/((m:ℝ)+1) := by field_simp;ring
  have hCoeff : 1-1/(m:ℝ)≤(m:ℝ)/((m:ℝ)+1) := by rw [hEq];linarith only [hInv]
  have hCMul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCoeff hC) hM
  calc
    _ = C*(1-1/(m:ℝ))*M-D*M/(m:ℝ)-C*M*(2/(m:ℝ)) := by ring
    _ ≤ C*((m:ℝ)/((m:ℝ)+1))*M-D*M/(m:ℝ)-C*M*(2/(m:ℝ)) :=
      sub_le_sub_right (sub_le_sub_right hCMul _) _
    _ ≤ _ := hBound

end ProphetSecretary.Analysis
