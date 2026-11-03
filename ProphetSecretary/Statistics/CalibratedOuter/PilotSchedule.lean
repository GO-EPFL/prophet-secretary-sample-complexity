import ProphetSecretary.Statistics.OuterPilotStatistics
import ProphetSecretary.Statistics.CalibratedSampleBudget
import ProphetSecretary.Statistics.CalibrationCountCutoff

/-!
# The dyadic-logarithmic scale pilot

The same numerical order-statistic confidence applies to a pilot of
`6000 ceil(log₂(2m))` rounds. This is the scale pilot in `upouter:construction`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics.Calibration

def outerPilotRank (m : ℕ) : ℕ := 12 * Nat.clog 2 (2*m)
def outerPilotRounds (m : ℕ) : ℕ := 500*outerPilotRank m

lemma outerPilotRank_pos {m : ℕ} (hm : 1≤m) : 0<outerPilotRank m := by
  unfold outerPilotRank
  exact Nat.mul_pos (by decide) (Nat.clog_pos (by decide : 1 < 2) (by omega))

lemma outerPilotRounds_eq_scale (m : ℕ) : outerPilotRounds m = outerScalePilotRounds m := by
  unfold outerPilotRounds outerPilotRank outerScalePilotRounds
  omega

lemma outerPilotRounds_div (m : ℕ) : outerPilotRounds m/500=outerPilotRank m := by simp [outerPilotRounds]

/-- Source pilot confidence 1−1/m, for arbitrary real laws and their atoms. -/
theorem outerPilot_failure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1≤m) :
    (Measure.pi (fun _ : Fin (outerPilotRounds m) => μ)).real
      (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm))ᶜ≤1/(m:ℝ) := by
  have h := numericalPilot_failure_le_two_exp μ (outerPilotRank m) (outerPilotRank_pos hm)
  have hCeil : 12*Real.log (2*(m:ℝ))≤(outerPilotRank m:ℝ) := by
    simpa only [outerPilotRank,Nat.cast_mul,Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_left (log_le_clog_two (2*m) (by omega)) (by norm_num : (0 : ℝ) ≤ 12)
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hExp : Real.exp (-(outerPilotRank m:ℝ)/12)≤Real.exp (-Real.log (2*(m:ℝ))) :=
    Real.exp_le_exp.mpr (by linarith only [hCeil])
  have hScale : 2*Real.exp (-Real.log (2*(m:ℝ)))=1/(m:ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<2*(m:ℝ))]
    field_simp
  exact h.trans ((mul_le_mul_of_nonneg_left hExp (by norm_num)).trans_eq hScale)

theorem outerPilot_success_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1≤m) :
    1-1/(m:ℝ)≤(Measure.pi (fun _ : Fin (outerPilotRounds m) => μ)).real
      (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm)) := by
  have h : (Measure.pi (fun _ : Fin (500*outerPilotRank m) => μ)).real
      (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm))ᶜ≤1/(m:ℝ) := outerPilot_failure_probability μ hm
  rw [probReal_compl_eq_one_sub (measurableSet_numericalPilotSuccess μ _ _)] at h
  change 1-1/(m:ℝ)≤(Measure.pi (fun _ : Fin (500*outerPilotRank m) => μ)).real
    (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm))
  linarith only [h]

end ProphetSecretary.Statistics.Calibration
