import ProphetSecretary.Statistics.OuterTrainingBlocks

/-!
# An explicit linear budget threshold

For m at least 2,000,000,000 the exact pilot budget is at most m. Hence the
outer program uses at most 6m samples per distribution. The large explicit
threshold is uniform in the number and laws of the offers.
-/

open MeasureTheory
namespace ProphetSecretary.Statistics

lemma outerPilotRounds_le_of_large (m : ℕ) (hm : 2000000000≤m) : outerPilotRounds m≤m := by
  have hmR : (2000000000:ℝ)≤m := by exact_mod_cast hm
  have hx : (0:ℝ)<2*(m:ℝ) := by positivity
  have hLog0 : 0≤Real.log (2*(m:ℝ)) := Real.log_nonneg (by linarith)
  have hLog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at hLog
  have hProd := mul_nonneg (sub_nonneg.mpr hmR) (show (0:ℝ)≤m by positivity)
  have hSqrt : Real.sqrt (2*(m:ℝ))≤(m:ℝ)/24000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hProd]
  have hCeil := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤12) hLog0)
  have hQ : (outerPilotRounds m:ℝ)≤6000*Real.log (2*(m:ℝ))+500 := by
    simp only [outerPilotRounds,outerPilotRank,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hCeil]
  have hQR : (outerPilotRounds m:ℝ)≤(m:ℝ) := by
    nlinarith only [hQ,hLog,hSqrt,hmR]
  exact_mod_cast hQR

lemma outerSampleBudget_le_six_mul (m : ℕ) (hm : 2000000000≤m) : outerSampleBudget m≤6*m := by
  have h := outerPilotRounds_le_of_large m hm
  unfold outerSampleBudget
  omega

lemma outerSampleBudget_div_ten_le (k : ℕ) (hk : 20000000000≤k) : outerSampleBudget (k/10)≤k := by
  have hm : 2000000000≤k/10 := by omega
  have hBudget := outerSampleBudget_le_six_mul (k/10) hm
  omega

lemma twenty_mul_div_ten_ge (k : ℕ) (hk : 20≤k) : k≤20*(k/10) := by omega

lemma outer_deficit_div_ten_le {k : ℕ} (hk : 20≤k) {A : ℝ} (hA : 0≤A) :
    A/((k/10:ℕ):ℝ)≤20*A/(k:ℝ) := by
  have hmR : (0:ℝ)<((k/10:ℕ):ℝ) := by exact_mod_cast (show 0<k/10 by omega)
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hCompare : (k:ℝ)≤20*((k/10:ℕ):ℝ) := by exact_mod_cast twenty_mul_div_ten_ge k hk
  apply (div_le_div_iff₀ hmR hkR).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hCompare hA]

end ProphetSecretary.Statistics
