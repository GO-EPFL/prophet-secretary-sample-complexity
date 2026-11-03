import ProphetSecretary.Statistics.CalibrationWorkScales

/-!
# Public clock and mark grids

The clock scale suffices for both threshold perturbations and the collision
bound for the validation keys. The mark scale is chosen from the total
number of reserved marks. Both scales are computed from public integers.
-/

open Set

namespace ProphetSecretary.Statistics.Calibration

def calibrationClockDemand (n m zInv : ℕ) : ℕ :=
  m^3*(n+1)^2 + 392*zInv*(m+1)^3 + 20 + m

def calibrationClockBits (n m zInv : ℕ) : ℕ := Nat.clog 2 (calibrationClockDemand n m zInv)

lemma calibrationClockDemand_le_grid (n m zInv : ℕ) :
    calibrationClockDemand n m zInv ≤ 2^calibrationClockBits n m zInv :=
  Nat.le_pow_clog (by decide) _

lemma calibrationClockGrid_validation (n m zInv : ℕ) :
    m^3*n^2 ≤ 2^calibrationClockBits n m zInv := by
  apply le_trans _ (calibrationClockDemand_le_grid n m zInv)
  unfold calibrationClockDemand
  have h : m^3*n^2 ≤ m^3*(n+1)^2 := by gcongr; omega
  omega

lemma calibrationClockGrid_error {n m zInv : ℕ} (hm : 2≤m) {zlo : ℝ}
    (hz : zlo∈Ioo (0 : ℝ) (1/4)) (hzi : 1/zlo≤(zInv : ℝ)) :
    let δ : ℝ := 1/((2^calibrationClockBits n m zInv : ℕ) : ℝ)
    0≤δ ∧ δ≤1/(m : ℝ) ∧ δ≤1/20 ∧ 4*δ≤policyAccuracy m zlo/2 := by
  dsimp only
  let Q := ((2^calibrationClockBits n m zInv : ℕ) : ℝ)
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hD : (calibrationClockDemand n m zInv : ℝ)≤Q := by
    dsimp only [Q]
    exact_mod_cast calibrationClockDemand_le_grid n m zInv
  have hmQ : (m : ℝ)≤Q := by
    apply le_trans _ hD
    exact_mod_cast (show m≤calibrationClockDemand n m zInv by unfold calibrationClockDemand; omega)
  have h20Q : (20 : ℝ)≤Q := by
    apply le_trans _ hD
    exact_mod_cast (show 20≤calibrationClockDemand n m zInv by unfold calibrationClockDemand; omega)
  have hM : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  refine ⟨(one_div_pos.mpr hQ).le, (one_div_le_one_div hQ hM).mpr hmQ,
    (one_div_le_one_div hQ (by norm_num)).mpr h20Q,?_⟩
  let h := policyAccuracy m zlo
  have hh : 0<h := (policyAccuracy_mem hm hz).1
  have hInv := policyAccuracy_inv_le (m := m) hz.1
  have hL : 392*(zInv : ℝ)*((m : ℝ)+1)^3≤Q := by
    apply le_trans _ hD
    exact_mod_cast (show 392*zInv*(m+1)^3≤calibrationClockDemand n m zInv by
      unfold calibrationClockDemand
      omega)
  have hScale : 8/h≤Q := by
    calc
      _ = 8*h⁻¹ := by ring
      _ ≤ 8*((49/zlo)*((m : ℝ)+1)^3) := mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = (392*(1/zlo))*((m : ℝ)+1)^3 := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzi (by norm_num))
        (by positivity)).trans hL
  have he : 8≤Q*h := (div_le_iff₀ hh).mp hScale
  change 4*(1/Q)≤h/2
  apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  rw [show 4*(1/Q)*2=8/Q by ring]
  exact (div_le_iff₀ hQ).mpr (by simpa only [mul_comm] using he)

def outerMarkBits (n m : ℕ) : ℕ :=
  Nat.clog 2 (m^2*(n*(3*m+6000*Nat.clog 2 (2*m)+1))^2)

end ProphetSecretary.Statistics.Calibration
