import ProphetSecretary.Statistics.CalibrationTargetComparison
import ProphetSecretary.Model.SmallMeanClamp

/-!
# The pointwise reward bound for duration calibration

The surrogate duration is used only on the interior and the right extension.
On the left extension, the reward boundary clamp applies at the first
executed coefficient while the analytical coefficient is zero.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

noncomputable def normalizedCoefficient (z : ℝ) : ℝ := 1/(1+z)

lemma normalizedCoefficient_mem {z : ℝ} (hz : z∈Icc (0 : ℝ) (1/4)) :
    normalizedCoefficient z∈Icc (4/5 : ℝ) 1 := by
  have hd : 0<1+z := by linarith [hz.1]
  exact ⟨(le_div_iff₀ hd).mpr (by linarith [hz.2]),(div_le_one hd).mpr (by linarith [hz.1])⟩

lemma normalizedCoefficient_identities {z : ℝ} (hz : 0≤z) :
    normalizedCoefficient z*(1+z)=1 ∧ normalizedCoefficient z*z=1-normalizedCoefficient z ∧
    1/normalizedCoefficient z=1+z ∧ (1-normalizedCoefficient z)/normalizedCoefficient z=z := by
  have hd : (1+z)≠0 := by positivity
  have hlam : normalizedCoefficient z≠0 := by unfold normalizedCoefficient; positivity
  have h1 : normalizedCoefficient z*(1+z)=1 := by unfold normalizedCoefficient; field_simp
  have h2 : normalizedCoefficient z*z=1-normalizedCoefficient z := by nlinarith only [h1]
  exact ⟨h1,h2,(div_eq_iff hlam).mpr (by simpa only [mul_comm] using h1.symm),
    (div_eq_iff hlam).mpr (by simpa only [mul_comm] using h2.symm)⟩

lemma scalarGap_unnormalized_duration {n : ℕ} (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {z : ℝ} (hz : 0≤z) :
    optimalScalarValue P 1 z-optimalCompetitiveRatio*(P.expectedMaximum+z)=
      (1+z)*normalizedScalarGap P (normalizedCoefficient z) := by
  obtain ⟨h1,h2,_,_⟩ := normalizedCoefficient_identities hz
  have hs := optimalScalarValue_normalize P hP hz
  change optimalScalarValue P (normalizedCoefficient z) (z/(1+z)) =
    normalizedCoefficient z*optimalScalarValue P 1 z at hs
  rw [show z/(1+z)=normalizedCoefficient z*z by unfold normalizedCoefficient; ring,h2] at hs
  unfold normalizedScalarGap scalarGap
  rw [hs,← h2]
  calc
    _ = ((1+z)*normalizedCoefficient z)*(optimalScalarValue P 1 z-
      optimalCompetitiveRatio*(P.expectedMaximum+z)) := by rw [mul_comm (1+z),h1,one_mul]
    _ = _ := by ring

/-- The scalar master inequality away from the left extension. -/
theorem calibration_reward_master_nonleft {n : ℕ} (P : Instance n) (π : RandomizedPolicy n)
    (hP : P.HasPositiveFiniteMaximum) {mu z g ρ r : ℝ} (hM : mu≤P.expectedMaximum)
    (hM1 : P.expectedMaximum≤1) (hz : z∈Icc (0 : ℝ) (1/4))
    (hReg : optimalScalarValue P 1 z-π.scalarObjective P 1 z≤r)
    (hTime : π.expectedDuration P≤ρ+g) :
    mu*normalizedScalarGap P (normalizedCoefficient z)-r-z*g-
      (1/4)*max 0 (ρ-P.optimalScalarRatio) ≤ π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum := by
  let lam := normalizedCoefficient z
  have hlam := normalizedCoefficient_mem hz
  have hlam' : lam∈Icc (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ)≤4/5).trans hlam.1,hlam.2⟩
  have hlamI : lam∈Ioc (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ)<4/5).trans_le hlam.1,hlam.2⟩
  obtain ⟨_,_,hInv,hZ⟩ := normalizedCoefficient_identities hz.1
  have hAbsorb := P.scalarGap_ratioSlack_absorption hP hlamI
  rw [hInv,hZ] at hAbsorb
  let D := lam*P.expectedMaximum+1-lam
  have hD0 : 0<D := P.scalarRatio_denominator_pos hP.2 hlam'
  have hD1 : D≤1 := by dsimp [D]; linarith [mul_le_mul_of_nonneg_left hM1 hlam'.1]
  have hRatio : mu≤P.expectedMaximum/D := hM.trans ((le_div_iff₀ hD0).mpr
    (mul_le_of_le_one_right P.expectedMaximum_nonnegative hD1))
  have hAbsorb' := (mul_le_mul_of_nonneg_right hRatio (normalizedScalarGap_nonnegative P hP.1 hlam')).trans hAbsorb
  have hT := mul_le_mul_of_nonneg_left hTime hz.1
  have hError : z*(ρ-P.optimalScalarRatio)≤(1/4)*max 0 (ρ-P.optimalScalarRatio) :=
    (mul_le_mul_of_nonneg_left (le_max_right _ _) hz.1).trans
      (mul_le_mul_of_nonneg_right hz.2 (le_max_left _ _))
  rw [π.scalarObjective_eq P hP.1,one_mul] at hReg
  have hScale := scalarGap_unnormalized_duration P hP.1 hz.1
  linarith only [hAbsorb',hT,hError,hReg,hScale]

/-- On the left extension the executed policy is evaluated at the clamp endpoint. -/
theorem calibration_reward_master_left {n : ℕ} (P : Instance n) (π : RandomizedPolicy n)
    (hP : P.HasPositiveFiniteMaximum) {mu r : ℝ} (hmu : mu≤1/40)
    (hClamp : normalizedScalarGap P 1/40-5*r≤π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum) :
    mu*normalizedScalarGap P (normalizedCoefficient 0)-5*r ≤
      π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum := by
  have hF := normalizedScalarGap_nonnegative P hP.1 (show (1 : ℝ)∈Icc 0 1 by norm_num)
  have h := mul_le_mul_of_nonneg_right hmu hF
  have he : normalizedCoefficient 0=1 := by norm_num [normalizedCoefficient]
  rw [he]
  linarith only [h,hClamp]

end ProphetSecretary.Statistics.Calibration
