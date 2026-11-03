import ProphetSecretary.Statistics.ArithmeticCalibratedLearner
import ProphetSecretary.Statistics.CalibratedFairCalls

/-!
# Polynomial bounds on public query scales

A bound in terms of the public parameters also applies on exceptional sample
outcomes. The statistical guarantees do not enter any of these estimates.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Probability

lemma clog_two_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))

lemma calibration_level_tree_bound {m : ℕ} [NeZero m] {h : ℝ} (hh : h∈Ioo (0 : ℝ) 1) :
    (16 : ℝ)^calibrationPlannerLevel m h ≤ (6400 : ℝ)^4*(calibrationWeightBound m/h)^8 := by
  have hb := calibrationWeightBound_ge_one (m := m)
  unfold calibrationPlannerLevel scalarPlannerLevel
  rw [dif_pos (scalarPlannerPrecision_exists hb hh)]
  exact countedScalarPlannerLevel_tree_factor hb hh _

lemma targetAccuracy_inv (m : ℕ) : (1/(m : ℝ))⁻¹ = m := by simp

lemma policyAccuracy_inv_le {m : ℕ} {zlo : ℝ} (hz : 0<zlo) :
    (policyAccuracy m zlo)⁻¹ ≤ (49/zlo)*((m : ℝ)+1)^3 := by
  have hL : targetCountCutoff m ≤ 4*(m : ℝ)+2 := by
    unfold targetCountCutoff
    have hm : (Nat.clog 2 m : ℝ) ≤ m := by exact_mod_cast clog_two_le_self m
    linarith only [hm]
  have hL0 : 0 ≤ targetCountCutoff m := by unfold targetCountCutoff; positivity
  have hBase : 1+targetCountCutoff m ≤ 7*((m : ℝ)+1) := by
    linarith only [hL, Nat.cast_nonneg (α := ℝ) m]
  have hm : (m : ℝ) ≤ (m : ℝ)+1 := by linarith
  unfold policyAccuracy
  rw [inv_div]
  calc
    _ ≤ (((m : ℝ)+1)*(7*((m : ℝ)+1))^2)/zlo := by
      apply div_le_div_of_nonneg_right _ hz.le
      apply mul_le_mul hm (pow_le_pow_left₀ (by linarith) hBase _)
        (by positivity) (by positivity)
    _ = _ := by ring

lemma confidenceCopyCount_inv_le (D : ℕ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ 1/(D : ℝ))
    (hD : 0<D) : confidenceCopyCount (1/(D : ℝ)) H ≤ 2*D+1 := by
  have hpow : D ≤ 4^D := (Nat.le_of_lt (Nat.lt_two_pow_self (n := D))).trans
    (Nat.pow_le_pow_left (by decide : 2≤4) D)
  have hR : (D : ℝ) ≤ (4 : ℝ)^D := by exact_mod_cast hpow
  have h : (1/4 : ℝ)^D ≤ 1/(D : ℝ) := by
    rw [one_div_pow, one_div_le_one_div (by positivity : 0 < (4 : ℝ)^D) (by exact_mod_cast hD)]
    exact hR
  unfold confidenceCopyCount
  rw [(countedConfidenceLevel_spec _ H).1]
  have hmin := Nat.find_min' H h
  omega

lemma targetConfidenceCount_le (m : ℕ)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ 1/((m : ℝ)^2*(4*(m : ℝ)+1))) (hm : 0<m) :
    confidenceCopyCount (1/((m : ℝ)^2*(4*(m : ℝ)+1))) H ≤ 2*(m^2*(4*m+1))+1 := by
  let D := m^2*(4*m+1)
  have h : (D : ℝ)=(m : ℝ)^2*(4*(m : ℝ)+1) := by simp [D]
  simpa only [h,D] using confidenceCopyCount_inv_le D (by simpa only [h] using H) (by dsimp [D]; positivity)

lemma policyConfidenceCount_le (n m J : ℕ)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ policyFailureBound n m J) (hn : 0<n) (hm : 0<m) :
    confidenceCopyCount (policyFailureBound n m J) H ≤ 2*(m^2*n*(J+1))+1 := by
  let D := m^2*n*(J+1)
  have h : (D : ℝ)=(m : ℝ)^2*(n : ℝ)*((J : ℝ)+1) := by simp [D]
  simpa only [h,D,policyFailureBound] using confidenceCopyCount_inv_le D
    (by simpa only [h,policyFailureBound] using H) (by dsimp [D]; positivity)

end ProphetSecretary.Statistics.Calibration
