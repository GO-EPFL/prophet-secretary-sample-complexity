import ProphetSecretary.Statistics.CalibrationMasterPointwise
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# A rational lower coefficient for calibration

The uniform reward-boundary slack allows the clamp endpoint to be chosen
rational and strictly below one. The corresponding duration coefficient
is therefore rational and positive.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

/-- The left-extension clamp needed by the calibrated learner. -/
theorem exists_rational_calibration_endpoint (mu : ℝ) (hmu : 0<mu) :
    ∃ b : ℚ, (b : ℝ)∈Ioo (4/5 : ℝ) 1 ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum →
      ∀ (π : RandomizedPolicy n) (r : ℝ),
      π.normalizedRegret P (b : ℝ)≤r →
      normalizedScalarGap P 1/40-5*r≤π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum := by
  obtain ⟨d,hd,hBoundary⟩ := bounded_reward_boundary_slack 1 mu hmu
  have hL : max (4/5 : ℝ) (1-d/8)<1 := max_lt (by norm_num) (by linarith)
  obtain ⟨b,hb,ht⟩ := exists_rat_btwn hL
  have hLow : (4/5 : ℝ)<(b : ℝ) := (le_max_left _ _).trans_lt hb
  have hWidth : 8*(1-(b : ℝ))≤d := by linarith only [(le_max_right _ _).trans_lt hb]
  refine ⟨b,⟨hLow,ht⟩,?_⟩
  intro n P hcap hMean π r hr
  have hP := P.integrable_maximum_of_bounded hcap
  have hbI : (b : ℝ)∈Icc 0 1 := ⟨(by norm_num : (0 : ℝ)≤4/5).trans hLow.le,ht.le⟩
  have hOne : (1 : ℝ)∈Icc 0 1 := by norm_num
  have hD : d≤normalizedScalarGap P 1 := by rw [normalizedScalarGap_one]; exact hBoundary n P hcap hMean
  have hG := π.scalarGap_ge_gap_sub_projectedRegret P (H:=1) (by norm_num) hcap hOne hbI hr
  norm_num at hG
  rw [abs_of_nonneg (sub_nonneg.mpr ht.le)] at hG
  have hF0 := normalizedScalarGap_nonnegative P hP hOne
  have hr0 := (π.normalizedRegret_nonnegative P hP hbI).trans hr
  rw [π.scalarObjective_eq P hP] at hG
  linarith only [hG,hWidth,hD,hF0,hr0]

lemma calibrationEndpoint_coefficient_bounds {b : ℝ} (hb : b∈Ioo (4/5 : ℝ) 1) :
    (1-b)/b∈Ioo (0 : ℝ) (1/4) := by
  have hb0 : 0<b := (by norm_num : (0 : ℝ)<4/5).trans hb.1
  exact ⟨div_pos (sub_pos.mpr hb.2) hb0,(div_lt_iff₀ hb0).mpr (by linarith [hb.1])⟩

lemma calibrationEndpoint_normalized {b : ℝ} (hb : b∈Ioo (4/5 : ℝ) 1) :
    normalizedCoefficient ((1-b)/b)=b := by
  have hb0 : 0<b := (by norm_num : (0 : ℝ)<4/5).trans hb.1
  unfold normalizedCoefficient
  field_simp [hb0.ne']
  ring

end ProphetSecretary.Statistics.Calibration
