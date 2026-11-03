import ProphetSecretary.Statistics.CalibratedPreparedPolicy
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The coefficient grid for calibration

Its size is linear in the per-block budget. Both endpoints of a selected
nonleft segment are within one mesh interval of the coefficient used to
measure scalar regret.
-/

open Set

namespace ProphetSecretary.Statistics.Calibration

noncomputable def familyGridSize (m : ℕ) (zlo zhi : ℝ) : ℕ := ⌈(m : ℝ)*(zhi-zlo)⌉₊

lemma familyGridSize_pos {m : ℕ} (hm : 0<m) {zlo zhi : ℝ} (hz : zlo<zhi) :
    0<familyGridSize m zlo zhi := by
  have h : 0<(m : ℝ)*(zhi-zlo) := mul_pos (Nat.cast_pos.mpr hm) (sub_pos.mpr hz)
  unfold familyGridSize
  by_contra hn
  have he : ⌈(m : ℝ)*(zhi-zlo)⌉₊=0 := by omega
  simpa only [he,Nat.cast_zero,not_le_of_gt h] using Nat.le_ceil ((m : ℝ)*(zhi-zlo))

lemma familyGridSize_le {m : ℕ} {zlo zhi : ℝ} (hz : zhi-zlo≤1) : familyGridSize m zlo zhi ≤ m := by
  apply Nat.ceil_le.mpr
  nlinarith [mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg m)]

@[simp] lemma familyCoefficient_zero (zlo zhi : ℝ) (J : ℕ) : familyCoefficient zlo zhi J 0=zlo := by
  simp [familyCoefficient]

lemma familyCoefficient_last (zlo zhi : ℝ) {J : ℕ} (hJ : 0<J) :
    familyCoefficient zlo zhi J J=zhi := by
  simp only [familyCoefficient,min_self]
  rw [div_self (Nat.cast_ne_zero.mpr hJ.ne'),one_mul]
  ring

lemma familyCoefficient_range {zlo zhi : ℝ} (hz : zlo≤zhi) (J k : ℕ) :
    familyCoefficient zlo zhi J k ∈ Icc zlo zhi := by
  refine ⟨by simpa only [familyCoefficient_zero] using
    familyCoefficient_monotone hz J (Nat.zero_le k),?_⟩
  by_cases hJ : 0<J
  · have h := familyCoefficient_monotone hz J (Nat.le_max_right J k)
    rw [show familyCoefficient zlo zhi J (max J k)=familyCoefficient zlo zhi J J by
      simp [familyCoefficient]] at h
    rwa [familyCoefficient_last zlo zhi hJ] at h
  · have he : J=0 := by omega
    simpa [he,familyCoefficient] using hz

lemma familyCoefficient_mesh {m J : ℕ} (hm : 0<m) (hJ : 0<J)
    {zlo zhi : ℝ} (hSize : (m : ℝ)*(zhi-zlo) ≤ (J : ℝ))
    {k : ℕ} (hk : k<J) :
    familyCoefficient zlo zhi J (k+1)-familyCoefficient zlo zhi J k ≤ 1/(m : ℝ) := by
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr hm
  have hJR : (0 : ℝ)<J := Nat.cast_pos.mpr hJ
  have he : familyCoefficient zlo zhi J (k+1)-familyCoefficient zlo zhi J k =
      (zhi-zlo)/(J : ℝ) := by
    simp only [familyCoefficient,min_eq_left (Nat.succ_le_iff.mpr hk),min_eq_left hk.le,Nat.cast_succ]
    ring
  rw [he,div_le_div_iff₀ hJR hmR,one_mul,mul_comm]
  exact hSize

lemma familyGridSize_mesh {m : ℕ} (hm : 0<m) {zlo zhi : ℝ} (hz : zlo<zhi)
    {k : ℕ} (hk : k<familyGridSize m zlo zhi) :
    familyCoefficient zlo zhi (familyGridSize m zlo zhi) (k+1)-
      familyCoefficient zlo zhi (familyGridSize m zlo zhi) k ≤ 1/(m : ℝ) :=
  familyCoefficient_mesh hm (familyGridSize_pos hm hz) (Nat.le_ceil _) hk

lemma selectedCoefficient_range {zlo zhi : ℝ} (hz0 : 0≤zlo) (hz : zlo≤zhi)
    (J : ℕ) (p : ℕ × ℝ) (hα : p.2 ∈ Icc (0 : ℝ) 1) :
    selectedCoefficient zlo zhi J p ∈ Icc (0 : ℝ) zhi := by
  unfold selectedCoefficient
  split_ifs
  · exact ⟨le_rfl,hz0.trans hz⟩
  · have ha := familyCoefficient_range hz J (lowerPolicyIndex J p.1).val
    have hb := familyCoefficient_range hz J (upperPolicyIndex J p.1).val
    have hβ : 0≤1-p.2 := sub_nonneg.mpr hα.2
    constructor
    · exact add_nonneg (mul_nonneg hβ (hz0.trans ha.1)) (mul_nonneg hα.1 (hz0.trans hb.1))
    · linarith [mul_le_mul_of_nonneg_left ha.2 hβ,mul_le_mul_of_nonneg_left hb.2 hα.1]

lemma selectedCoefficient_last (zlo zhi : ℝ) {J : ℕ} (hJ : 0<J) (α : ℝ) :
    selectedCoefficient zlo zhi J (J+2,α)=zhi := by
  simp only [selectedCoefficient,show J+2≠1 by omega,if_false,lowerPolicyIndex_last,
    upperPolicyIndex_last,Fin.val_last,familyCoefficient_last zlo zhi hJ]
  ring

lemma selectedCoefficient_distance_endpoints {m J : ℕ} (hm : 0<m) (hJ : 0<J)
    {zlo zhi : ℝ} (hz : zlo≤zhi) (hSize : (m : ℝ)*(zhi-zlo) ≤ (J : ℝ))
    {k : ℕ} (hk0 : 2≤k) (hk1 : k≤J+2) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    |selectedCoefficient zlo zhi J (k,α)-familyCoefficient zlo zhi J (lowerPolicyIndex J k).val| ≤ 1/(m : ℝ) ∧
    |selectedCoefficient zlo zhi J (k,α)-familyCoefficient zlo zhi J (upperPolicyIndex J k).val| ≤ 1/(m : ℝ) := by
  by_cases hk : k=J+2
  · subst k
    simp only [selectedCoefficient_last zlo zhi hJ,lowerPolicyIndex_last,upperPolicyIndex_last,Fin.val_last,
      familyCoefficient_last zlo zhi hJ,sub_self,abs_zero]
    exact ⟨by positivity,by positivity⟩
  · have ha : (lowerPolicyIndex J k).val=k-2 := by simp only [lowerPolicyIndex]; omega
    have hb : (upperPolicyIndex J k).val=k-2+1 := by simp only [upperPolicyIndex]; omega
    let A := familyCoefficient zlo zhi J (k-2)
    let B := familyCoefficient zlo zhi J (k-2+1)
    have hAB : A≤B := familyCoefficient_monotone hz J (by omega)
    have hd : B-A≤1/(m : ℝ) := familyCoefficient_mesh hm hJ hSize (by omega)
    have hZ : selectedCoefficient zlo zhi J (k,α)=(1-α)*A+α*B := by
      simp only [selectedCoefficient,show k≠1 by omega,if_false,ha,hb,A,B]
    have h1 : selectedCoefficient zlo zhi J (k,α)-A=α*(B-A) := by rw [hZ]; ring
    have h2 : selectedCoefficient zlo zhi J (k,α)-B=-(1-α)*(B-A) := by rw [hZ]; ring
    rw [ha,hb,h1,h2,abs_of_nonneg (mul_nonneg hα.1 (sub_nonneg.mpr hAB))]
    rw [show -(1-α)*(B-A) = -((1-α)*(B-A)) by ring,abs_neg,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hAB))]
    exact ⟨(mul_le_of_le_one_left (sub_nonneg.mpr hAB) hα.2).trans hd,
      (mul_le_of_le_one_left (sub_nonneg.mpr hAB) (by linarith [hα.1])).trans hd⟩

end ProphetSecretary.Statistics.Calibration
