import ProphetSecretary.Statistics.FairCalibratedNativeCalls
import ProphetSecretary.Statistics.CalibratedPolynomialWork
import ProphetSecretary.Statistics.FiniteBitLearner

/-!
# Uniform bounds on finite query and clock parameters

The fair query depth uses half its requested tolerance for stochastic
error. The clock-rounded threshold query already has half the original
policy tolerance. Both changes affect only the public constants.
-/

open Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Probability

variable {n m : ℕ}

lemma calibrationFairPrecision_le_inv_grid (n m : ℕ) [NeZero m] (h : ℝ) (hh : h∈Ioo (0 : ℝ) 1) :
    (calibrationFairPrecision n m h hh : ℝ) ≤ 2/plannerGridTolerance n (calibrationWeightBound m) h+3 := by
  let β := calibrationWeightBound m
  let δ := plannerGridTolerance n β h
  have hβ := calibrationWeightBound_ge_one (m := m)
  have hδ := plannerGridTolerance_pos n (zero_lt_one.trans_le hβ) hh.1
  have hδ1 := plannerGridTolerance_lt_one n hβ hh.2.le
  have hlog4 : 1≤Real.log 4 := by
    have h := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans (show (3 : ℝ)≤4 by norm_num))
    simpa only [Real.log_exp] using h
  have hlog : 0≤Real.log (1/δ) := Real.log_nonneg
    ((one_le_div hδ).mpr (by simpa only [one_mul] using hδ1.le))
  have hC := (countedPlannerBitPrecision_correct n hβ hh.1 hh.2.le
    (exists_confidence_level hδ hδ1)).2.2.1
  have hC' : (calibrationFairPrecision n m h hh : ℝ)<
      2*(Real.log (1/δ)/Real.log 4)+3 := hC
  have hDiv : Real.log (1/δ)/Real.log 4≤1/δ :=
    (div_le_self hlog hlog4).trans (Real.log_le_self (by positivity))
  change _ ≤ 2/δ+3
  exact hC'.le.trans (by
    rw [show 2/δ=2*(1/δ) by ring]
    exact add_le_add (mul_le_mul_of_nonneg_left hDiv (by norm_num)) le_rfl)

noncomputable def finiteLevelConstant (zlo : ℝ) : ℝ :=
  (6400 : ℝ)^4*((4 : ℝ)^8*2^32*(2+196/zlo))^8

lemma finiteTargetLevel_bound (a : FairCalibrationParameters n m) :
    (16 : ℝ)^a.nativeTargetSchedule.level≤finiteLevelConstant a.zlo*((m : ℝ)+1)^280 := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  rw [a.nativeTargetSchedule_level]
  have hh : a.targetTolerance/2∈Ioo (0 : ℝ) 1 :=
    ⟨by linarith [a.targetTolerance_mem.1],by linarith [a.targetTolerance_mem.2]⟩
  apply calibrationLevel_poly hh (by have := a.coefficient_mem.1; positivity)
  have hInv : (a.targetTolerance/2)⁻¹=2*(m : ℝ) := by
    unfold FairCalibrationParameters.targetTolerance
    rw [inv_div,div_eq_mul_inv,targetAccuracy_inv]
  have hM : (m : ℝ)≤((m : ℝ)+1)^3 := by
    apply (show (m : ℝ)≤(m : ℝ)+1 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ)≤(m : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) m]) (by omega : 1≤3)
  rw [hInv]
  exact mul_le_mul (by linarith [div_nonneg (by norm_num : (0 : ℝ)≤196) a.coefficient_mem.1.le])
    hM (Nat.cast_nonneg _) (by have := a.coefficient_mem.1; positivity)

lemma finiteThresholdLevel_bound (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :
    (16 : ℝ)^(a.nativeThresholdSchedule zlo hz).level≤finiteLevelConstant a.zlo*((m : ℝ)+1)^280 := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  rw [a.nativeThresholdSchedule_level zlo hz]
  have hh : a.thresholdTolerance/2∈Ioo (0 : ℝ) 1 :=
    ⟨by linarith [a.thresholdTolerance_mem.1],by linarith [a.thresholdTolerance_mem.2]⟩
  apply calibrationLevel_poly hh (by have := a.coefficient_mem.1; positivity)
  have hInv := policyAccuracy_inv_le (m := m) a.coefficient_mem.1
  have h : (a.thresholdTolerance/2)⁻¹=4*(policyAccuracy m a.zlo)⁻¹ := by
    unfold FairCalibrationParameters.thresholdTolerance
    rw [inv_div,div_eq_mul_inv,inv_div,div_eq_mul_inv]
    ring
  rw [h]
  calc
    _ ≤ 4*((49/a.zlo)*((m : ℝ)+1)^3) := mul_le_mul_of_nonneg_left hInv (by norm_num)
    _ = (196/a.zlo)*((m : ℝ)+1)^3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma finiteClockBits_polynomial (a : FairCalibrationParameters n m) :
    a.clockBits≤(400*(a.clockInverse+1))*(n+m+2)^5 := by
  apply (clog_two_le_self (calibrationClockDemand n m a.clockInverse)).trans
  let N := n+m+2
  let z := a.clockInverse
  have hm : m≤N := by dsimp [N]; omega
  have hm1 : m+1≤N := by dsimp [N]; omega
  have hn1 : n+1≤N := by dsimp [N]; omega
  have hN : 0<N := by dsimp [N]; omega
  have h5 : 1≤N^5 := Nat.one_le_pow _ _ hN
  have h1 : N≤N^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hN (by omega : 1≤5)
  have h3 : N^3≤N^5 := Nat.pow_le_pow_right hN (by omega)
  have hA : m^3*(n+1)^2≤N^5 := by
    rw [show (5 : ℕ)=3+2 by decide,pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hm _) (Nat.pow_le_pow_left hn1 _)
  have hB : 392*z*(m+1)^3≤392*z*N^5 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hm1 _).trans h3)
  have hC : m≤N^5 := hm.trans h1
  change m^3*(n+1)^2+392*z*(m+1)^3+20+m≤400*(z+1)*N^5
  calc
    _ ≤ N^5+392*z*N^5+20*N^5+N^5 := by omega
    _ ≤ _ := by
      have hZ : 392*z+22≤400*(z+1) := by omega
      have hEq : N^5+392*z*N^5+20*N^5+N^5=(392*z+22)*N^5 := by ring
      rw [hEq]
      exact Nat.mul_le_mul_right _ hZ

lemma calibrationFairPrecision_polynomial (n m : ℕ) [NeZero m] {h A : ℝ}
    (hh : h∈Ioo (0 : ℝ) 1) (hA : 0≤A) (hInv : h⁻¹≤A*((m : ℝ)+1)^3) :
    (calibrationFairPrecision n m h hh : ℝ) ≤
      (40*((4 : ℝ)^8*2^32*A)+3)*((n : ℝ)+m+2)^36 := by
  let N := (n : ℝ)+m+2
  let B := (4 : ℝ)^8*2^32
  let β := calibrationWeightBound m
  have hn : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hm : (0 : ℝ)≤m := Nat.cast_nonneg m
  have hN : 1≤N := by dsimp [N]; linarith only [hn,hm]
  have hNM : (m : ℝ)+1≤N := by dsimp [N]; linarith only [hn]
  have hb : β≤B*N^32 :=
    (calibrationWeightBound_poly m).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNM _) (by positivity))
  have hi : h⁻¹≤A*N^3 :=
    hInv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNM _) hA)
  have hn' : 10*(n : ℝ)+4≤14*N := by dsimp [N]; linarith only [hn,hm]
  have hb0 : 0≤β := zero_le_one.trans (calibrationWeightBound_ge_one (m := m))
  have hMul : β*(10*(n : ℝ)+4)*h⁻¹≤(B*N^32)*(14*N)*(A*N^3) :=
    mul_le_mul (mul_le_mul hb hn' (by positivity) (by positivity))
      hi (inv_pos.mpr hh.1).le (by positivity)
  have hAlg : 2/plannerGridTolerance n β h=(8/3)*(β*(10*(n : ℝ)+4)*h⁻¹) := by
    unfold plannerGridTolerance
    rw [div_div_eq_mul_div]
    ring
  calc
    _ ≤ 2/plannerGridTolerance n β h+3 := calibrationFairPrecision_le_inv_grid n m h hh
    _ = (8/3)*(β*(10*(n : ℝ)+4)*h⁻¹)+3 := by rw [hAlg]
    _ ≤ (8/3)*((B*N^32)*(14*N)*(A*N^3))+3 :=
      add_le_add (mul_le_mul_of_nonneg_left hMul (by norm_num)) le_rfl
    _ = ((112/3)*(B*A))*N^36+3 := by
      rw [show (36 : ℕ)=32+1+3 by decide,pow_add,pow_add,pow_one]
      have h : ((112/3 : ℝ))=(8/3)*14 := by norm_num
      rw [h]
      ac_rfl
    _ ≤ (40*(B*A)+3)*N^36 := by
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) (by positivity))
        (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hN))

private lemma confidenceCopyCount_congr {p q : ℝ} (e : p=q)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j≤p) (G : ∃ j : ℕ, (1/4 : ℝ)^j≤q) :
    confidenceCopyCount p H=confidenceCopyCount q G := by subst q; rfl

lemma finiteTargetCopies_bound (a : FairCalibrationParameters n m) :
    confidenceCopyCount a.nativeTargetSchedule.failure a.nativeTargetSchedule.confidence+1 ≤
      12*(n+m+2)^4 := by
  let p := a.nativeTargetSchedule.failure
  let H := a.nativeTargetSchedule.confidence
  let G := exists_confidence_level a.targetFailure_range.1 a.targetFailure_range.2
  have h : (p : ℝ)=a.targetFailure := a.rationalTargetFailure_cast
  let H' := (exists_quarter_pow_le_ratCast p).mpr H
  have hC := confidenceCopyCount_ratCast p H H'
  change confidenceCopyCount p H+1≤_
  rw [← hC,confidenceCopyCount_congr h H' G]
  exact targetCopies_poly n m (by have := a.two_le; omega) G

lemma finiteThresholdCopies_bound (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :
    confidenceCopyCount (a.nativeThresholdSchedule zlo hz).failure
      (a.nativeThresholdSchedule zlo hz).confidence+1≤12*(n+m+2)^4 := by
  let p := (a.nativeThresholdSchedule zlo hz).failure
  let H := (a.nativeThresholdSchedule zlo hz).confidence
  let G := exists_confidence_level a.thresholdFailure_range.1 a.thresholdFailure_range.2
  have h : (p : ℝ)=a.thresholdFailure := a.rationalThresholdFailure_cast zlo hz
  let H' := (exists_quarter_pow_le_ratCast p).mpr H
  have hC := confidenceCopyCount_ratCast p H H'
  change confidenceCopyCount p H+1≤_
  rw [← hC,confidenceCopyCount_congr h H' G]
  have hJ : a.grid≤m := familyGridSize_le (by linarith [a.coefficient_mem.1])
  exact thresholdCopies_poly n m a.grid a.nonempty (by have := a.two_le; omega) hJ G

noncomputable def finiteQueryBitConstant (zlo : ℝ) : ℝ := 40*((4 : ℝ)^8*2^32*(1+98/zlo))+3

lemma finiteTargetBits_bound (a : FairCalibrationParameters n m) :
    (a.nativeTargetSchedule.bits : ℝ)≤finiteQueryBitConstant a.zlo*((n : ℝ)+m+2)^36 := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  rw [a.nativeTargetSchedule_bits]
  have hA : (0 : ℝ)≤1+98/a.zlo := by have := a.coefficient_mem.1; positivity
  apply calibrationFairPrecision_polynomial n m a.targetTolerance_mem hA
  change (1/(m : ℝ))⁻¹≤_
  rw [targetAccuracy_inv]
  have hM : (m : ℝ)≤((m : ℝ)+1)^3 := by
    apply (show (m : ℝ)≤(m : ℝ)+1 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ)≤(m : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) m]) (by omega : 1≤3)
  exact hM.trans (le_mul_of_one_le_left (by positivity)
    (by linarith [div_nonneg (by norm_num : (0 : ℝ)≤98) a.coefficient_mem.1.le]))

lemma finiteThresholdBits_bound (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :
    ((a.nativeThresholdSchedule zlo hz).bits : ℝ)≤finiteQueryBitConstant a.zlo*((n : ℝ)+m+2)^36 := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  rw [a.nativeThresholdSchedule_bits zlo hz]
  have hA : (0 : ℝ)≤1+98/a.zlo := by have := a.coefficient_mem.1; positivity
  apply calibrationFairPrecision_polynomial n m a.thresholdTolerance_mem hA
  have hInv := policyAccuracy_inv_le (m := m) a.coefficient_mem.1
  change (policyAccuracy m a.zlo/2)⁻¹≤_
  rw [inv_div,div_eq_mul_inv]
  calc
    _ ≤ 2*((49/a.zlo)*((m : ℝ)+1)^3) := mul_le_mul_of_nonneg_left hInv (by norm_num)
    _ = (98/a.zlo)*((m : ℝ)+1)^3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma finiteCoinBits_bound (a : FairCalibrationParameters n m) : a.coinBits≤(n+m+2)^2 :=
  (clog_two_le_self (m^2)).trans (Nat.pow_le_pow_left (by omega) _)

lemma finiteOuterMarkSlots_bound (n m : ℕ) : outerMarkSlotCount n m≤12004*(n+m+2)^2 := by
  let N := n+m+2
  have h : outerSampleBudget m+1≤12004*N := by
    rw [outerSampleBudget_eq]
    have hClog := clog_two_le_self (2*m)
    dsimp [N]
    omega
  change n*(outerSampleBudget m+1)≤_
  calc
    _ ≤ N*(12004*N) := Nat.mul_le_mul (by dsimp [N]; omega) h
    _ = _ := by ring

lemma finiteOuterMarkBits_bound (n m : ℕ) : outerMarkBits n m≤12004^2*(n+m+2)^6 := by
  let N := n+m+2
  have h : outerMarkBits n m≤m^2*(outerMarkSlotCount n m)^2 := by
    unfold outerMarkBits
    apply (clog_two_le_self _).trans
    change m^2*(n*(3*m+6000*Nat.clog 2 (2*m)+1))^2≤m^2*(n*(outerSampleBudget m+1))^2
    rw [outerSampleBudget_eq]
  calc
    _ ≤ m^2*(outerMarkSlotCount n m)^2 := h
    _ ≤ N^2*(12004*N^2)^2 := Nat.mul_le_mul
      (Nat.pow_le_pow_left (by dsimp [N]; omega) _) (Nat.pow_le_pow_left (finiteOuterMarkSlots_bound n m) _)
    _ = _ := by ring

end ProphetSecretary.Statistics.Calibration
