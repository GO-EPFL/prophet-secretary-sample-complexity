import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating a logarithmic tail envelope

A tail bounded by L below α and by log(T/t)+3 above α has integral at most
Lα+log T+4 on (0,1]. The singular logarithm is integrable and its integral
is evaluated using the actual library theorem for the logarithm.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Analysis

theorem integral_log_tail_envelope {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc (0 : ℝ) 1))
    {α L T : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hT : 1 ≤ T)
    (hlow : ∀ t ∈ Ioc (0 : ℝ) 1, t ≤ α → f t ≤ L)
    (hhigh : ∀ t ∈ Ioc (0 : ℝ) 1, α < t → f t ≤ Real.log (T / t) + 3) :
    (∫ t in Ioc (0 : ℝ) 1, f t) ≤ L * α + Real.log T + 4 := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hμ : μ.real univ = 1 := by
    simp [μ, Measure.real, Real.volume_Ioc]
  have hlogI : Integrable Real.log μ := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).1
  have hlog : (∫ t, Real.log t ∂μ) = -1 := by
    change (∫ t in Ioc (0 : ℝ) 1, Real.log t) = _
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_log]
    norm_num
  let H : ℝ → ℝ := fun t => (Iic α).indicator (fun _ => L) t
  let G : ℝ → ℝ := fun t => Real.log T - Real.log t + 3
  have hHI : Integrable H μ := (integrable_const L).indicator measurableSet_Iic
  have hGI : Integrable G μ := ((integrable_const (Real.log T)).sub hlogI).add (integrable_const 3)
  have hHval : (∫ t, H t ∂μ) = α * L := by
    rw [integral_indicator_const L measurableSet_Iic]
    have heq : Iic α ∩ Ioc (0 : ℝ) 1 = Ioc 0 α := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · intro hx; exact ⟨hx.2.1, hx.1⟩
      · intro hx; exact ⟨hx.2, hx.1, hx.2.trans hα1⟩
    have hv : μ.real (Iic α) = α := by
      simp only [μ, Measure.real, Measure.restrict_apply measurableSet_Iic, heq,
        Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hα0]
    rw [hv, smul_eq_mul]
  have hGval : (∫ t, G t ∂μ) = Real.log T + 4 := by
    change (∫ t, (Real.log T - Real.log t) + 3 ∂μ) = _
    rw [integral_add (f := fun t => Real.log T - Real.log t) (g := fun _ : ℝ => (3 : ℝ))
      ((integrable_const _).sub hlogI) (integrable_const _),
      integral_sub (f := fun _ : ℝ => Real.log T) (g := Real.log) (integrable_const _) hlogI,
      integral_const, integral_const, hμ, hlog]
    simp only [one_smul]
    ring
  have hp : f ≤ᵐ[μ] (fun t => H t + G t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
    by_cases hta : t ≤ α
    · have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
      have hlogT := Real.log_nonneg hT
      have hGt : 0 ≤ G t := by dsimp [G]; linarith only [hlogt, hlogT]
      have hHt : H t = L := Set.indicator_of_mem (show t ∈ Iic α from hta) _
      rw [hHt]
      exact (hlow t ht hta).trans (le_add_of_nonneg_right hGt)
    · have hHt : H t = 0 := Set.indicator_of_notMem (show t ∉ Iic α from hta) _
      rw [hHt, zero_add]
      have hh := hhigh t ht (lt_of_not_ge hta)
      rw [Real.log_div hT0.ne' ht.1.ne'] at hh
      exact hh
  have hint := integral_mono_ae hf (hHI.add hGI) hp
  change (∫ t, f t ∂μ) ≤ (∫ t, H t + G t ∂μ) at hint
  rw [integral_add hHI hGI, hHval, hGval] at hint
  nlinarith only [hint]

end ProphetSecretary.Analysis
