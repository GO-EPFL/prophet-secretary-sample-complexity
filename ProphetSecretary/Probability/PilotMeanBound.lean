import ProphetSecretary.Probability.BoundedTailIntegrability

/-!
# Averaging a pilot tail comparison

The level comparison is integrated with every integrability obligation
explicit. The factor two on the reference mean comes from remaining threshold
s/2. This is the layer-cake step in `eq:bayes-pilot`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem pilot_mean_le {X Z : Ω → ℝ} (hX : Integrable X μ) (hZ : Integrable Z μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    {H : ℝ} (hZBound : ∀ᵐ ω ∂μ, Z ω ≤ H)
    {W : ℝ} (hW : 0 ≤ W) {q : ℝ → ℝ}
    (hq : ∀ s∈Ioi (0 : ℝ), 0 ≤ q s) (hqI : IntegrableOn q (Ioi 0))
    (hTail : ∀ s, W ≤ s → μ.real {ω | s < X ω} ≤ μ.real {ω | s/2 < Z ω}+2*q s) :
    (∫ ω, X ω ∂μ) ≤ W+2*(∫ ω, Z ω ∂μ)+2*(∫ s in Ioi (0 : ℝ), q s) := by
  let T := fun s : ℝ => μ.real {ω | s < Z ω}
  let B := (Ioc (0 : ℝ) W).indicator (fun _ : ℝ => (1 : ℝ))
  have hBI : Integrable B := (integrable_indicator_iff measurableSet_Ioc).mpr (integrable_const 1)
  have hBInt : (∫ s in Ioi (0 : ℝ), B s) = W := by
    rw [show B = (Ioc (0 : ℝ) W).indicator (fun _ : ℝ => (1 : ℝ)) from rfl,
      integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr Ioc_subset_Ioi_self,integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hW,sub_zero]
  have hTI : IntegrableOn T (Ioi 0) := integrableOn_real_strict_tail_of_bounded hZBound
  have hScaledI : IntegrableOn (fun s : ℝ => T (s/2)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff T 0 (by norm_num : (0 : ℝ) < 1/2)).mpr
      (by simpa only [mul_zero] using hTI)
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using h
  have hScaledInt : (∫ s in Ioi (0 : ℝ), T (s/2)) = 2*(∫ ω, Z ω ∂μ) := by
    have h := integral_comp_mul_left_Ioi T 0 (by norm_num : (0 : ℝ) < 1/2)
    norm_num only [mul_zero,inv_div,inv_one,smul_eq_mul] at h
    rw [hZ.integral_eq_integral_meas_lt hZ0]
    simpa only [T,div_eq_mul_inv,one_mul,mul_comm] using h
  have hBI' : IntegrableOn (fun s : ℝ => B s) (Ioi 0) := hBI.integrableOn
  have hSumI : IntegrableOn (fun s : ℝ => B s+T (s/2)) (Ioi 0) := hBI'.add hScaledI
  have hRhsI : IntegrableOn (fun s : ℝ => B s+T (s/2)+2*q s) (Ioi 0) :=
    hSumI.add (hqI.const_mul 2)
  have hPoint : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      μ.real {ω | s < X ω} ≤ B s+T (s/2)+2*q s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    by_cases hsW : s ≤ W
    · have hB : B s = 1 := Set.indicator_of_mem (show s∈Ioc (0 : ℝ) W from ⟨hs,hsW⟩) _
      rw [hB]
      have hP := real_strict_tail_le_one (μ := μ) X s
      have hT : 0 ≤ T (s/2) := measureReal_nonneg
      have hQ := hq s hs
      linarith
    · have hB : B s = 0 := Set.indicator_of_notMem (show s∉Ioc (0 : ℝ) W from fun h => hsW h.2) _
      rw [hB,zero_add]
      exact hTail s (le_of_not_ge hsW)
  rw [hX.integral_eq_integral_meas_lt hX0]
  calc
    _ ≤ ∫ s in Ioi (0 : ℝ), (B s+T (s/2)+2*q s) :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => measureReal_nonneg) hRhsI hPoint
    _ = _ := by
      rw [integral_add hSumI (hqI.const_mul 2),
        integral_add hBI' hScaledI,integral_const_mul,hBInt,hScaledInt]

end ProphetSecretary.Probability
