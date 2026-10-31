import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing logarithmic errors in the large-first-moment response

The analytic thresholds depend only on the numerical slack and error
constants. They are independent of the offer instance and its size.
-/

open Filter
open scoped Topology
namespace ProphetSecretary.Analysis

lemma tendsto_log_six_div_sqrt :
    Tendsto (fun x : ℝ => (Real.log x)^6/Real.sqrt x) atTop (𝓝 (0 : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s:=(1/2 : ℝ)) (6 : ℝ) (by norm_num)).tendsto_div_nhds_zero
  have hNat (x : ℝ) : (Real.log x)^(6 : ℝ)=(Real.log x)^6 := Real.rpow_natCast _ 6
  simpa only [hNat,← Real.sqrt_eq_rpow] using h

lemma logarithmic_error_product_le {x K : ℝ} (hx : 1≤x) (hLog : 1≤Real.log x) (hK : 0≤K) :
    (K*(1+(2*Real.log x)*(1+2*Real.log x))/x+1/Real.sqrt x)*(1+2*Real.log x)^4 ≤
      (3^6*(K+1))*((Real.log x)^6/Real.sqrt x) := by
  let l := Real.log x
  let b := 1+2*l
  have hl : 0≤l := (by norm_num : (0 : ℝ)≤1).trans hLog
  have hb : 0≤b := by dsimp only [b]; positivity
  have hbOne : 1≤b := by dsimp only [b]; linarith only [hl]
  have hbLe : b≤3*l := by dsimp only [b]; linarith only [hLog]
  have hb2 : 1≤b^2 := by nlinarith only [hbOne]
  have hPoly : 1+2*l*b≤b^2 := by dsimp only [b]; nlinarith only [hl]
  have hPoly4 : (1+2*l*b)*b^4≤b^6 := by
    calc
      _ ≤ b^2*b^4 := mul_le_mul_of_nonneg_right hPoly (pow_nonneg hb _)
      _ = _ := by ring
  have hFour : b^4≤b^6 := by
    calc
      _ = 1*b^4 := by ring
      _ ≤ b^2*b^4 := mul_le_mul_of_nonneg_right hb2 (pow_nonneg hb _)
      _ = _ := by ring
  have hSix : b^6≤3^6*l^6 := by
    calc
      _ ≤ (3*l)^6 := pow_le_pow_left₀ hb hbLe _
      _ = _ := by ring
  have hxP : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hRoot : 0<Real.sqrt x := Real.sqrt_pos.mpr hxP
  have hRootLe : Real.sqrt x≤x := Real.sqrt_le_self_iff.mpr (Or.inr hx)
  change (K*(1+2*l*b)/x+1/Real.sqrt x)*b^4 ≤ _
  calc
    _ = K*((1+2*l*b)*b^4)/x+b^4/Real.sqrt x := by ring
    _ ≤ K*(b^6/Real.sqrt x)+b^6/Real.sqrt x := by
      apply add_le_add
      · calc
          _ ≤ K*b^6/x := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPoly4 hK) hxP.le
          _ ≤ K*b^6/Real.sqrt x := div_le_div_of_nonneg_left (mul_nonneg hK (pow_nonneg hb _)) hRoot hRootLe
          _ = _ := by ring
      · exact div_le_div_of_nonneg_right hFour hRoot.le
    _ = (K+1)*b^6/Real.sqrt x := by ring
    _ ≤ (K+1)*(3^6*l^6)/Real.sqrt x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSix (by linarith only [hK])) hRoot.le
    _ = _ := by ring

theorem exists_largeFirstMomentSurplus_threshold {A K : ℝ} (hA : 0<A) (hK : 0≤K) :
    ∃ m0 : ℕ, 65536≤m0 ∧ ∀ m : ℕ, m0≤m →
      0≤A/(1+2*Real.log (m : ℝ))^4-
        K*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ)-1/Real.sqrt (m : ℝ) := by
  have hLimit : Tendsto (fun m : ℕ => (3^6*(K+1))*((Real.log (m : ℝ))^6/Real.sqrt (m : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    have hCast : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h := (tendsto_log_six_div_sqrt.const_mul (3^6*(K+1))).comp hCast
    rw [mul_zero] at h
    exact h
  have hSmall := hLimit.eventually (gt_mem_nhds hA)
  have hLogs : ∀ᶠ m : ℕ in atTop, 1≤Real.log (m : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hEvent : ∀ᶠ m : ℕ in atTop, 65536≤m ∧
      0≤A/(1+2*Real.log (m : ℝ))^4-
        K*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ)-1/Real.sqrt (m : ℝ) := by
    filter_upwards [hSmall,hLogs,eventually_ge_atTop (65536 : ℕ)] with m hSmall hLog hm
    refine ⟨hm,?_⟩
    have hmOne : (1 : ℝ)≤m := by exact_mod_cast (show 1≤m by omega)
    have hBound := (logarithmic_error_product_le hmOne hLog hK).trans hSmall.le
    have hB : 0<(1+2*Real.log (m : ℝ))^4 := by
      apply pow_pos
      linarith only [hLog]
    have hCost := (le_div_iff₀ hB).mpr hBound
    linarith only [hCost]
  obtain ⟨m0,hm0⟩ := eventually_atTop.mp hEvent
  exact ⟨m0,(hm0 m0 le_rfl).1,fun m hm => (hm0 m hm).2⟩

end ProphetSecretary.Analysis
