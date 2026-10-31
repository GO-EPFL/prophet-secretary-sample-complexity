import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing the probability-mesh error into the sample rate

A mean floor μ>0 converts the additive m⁻² reward error into a competitive
ratio loss. The constants depend only on μ and the rate deficit, with no
instance-size or alphabet-size dependence.
-/

namespace ProphetSecretary.Analysis

lemma reciprocal_square_le_reciprocal {m : ℝ} (hm : 1≤m) : 1/m^2≤1/m := by
  have hmP : 0<m := lt_of_lt_of_le zero_lt_one hm
  exact one_div_le_one_div_of_le hmP (by nlinarith only [hm])

lemma mesh_reward_deficit_absorption {m μ M A C γ E : ℝ} (hm : 1≤m) (hμ : 0<μ) (hM : μ≤M)
    (hRate : C-A/m≤γ) (hReward : γ*M-1/m^2≤E) :
    (C-(A+1/μ)/m)*M≤E := by
  have hmP : 0<m := lt_of_lt_of_le zero_lt_one hm
  have hMP : 0≤M := hμ.le.trans hM
  have hTiny : 1/m^2≤M/(μ*m) := by
    apply (reciprocal_square_le_reciprocal hm).trans
    apply (div_le_div_iff₀ hmP (mul_pos hμ hmP)).mpr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hmP.le
  have hIdentity : (C-(A+1/μ)/m)*M=(C-A/m)*M-M/(μ*m) := by
    field_simp
    ring
  rw [hIdentity]
  exact (sub_le_sub (mul_le_mul_of_nonneg_right hRate hMP) hTiny).trans hReward

lemma mesh_reach_deficit_absorption {m A C γ q : ℝ} (hm : 1≤m)
    (hRate : C-A/m≤γ) (hReach : γ-1/m^2≤q) : C-(A+1)/m≤q := by
  have hIdentity : C-(A+1)/m=(C-A/m)-1/m := by ring
  rw [hIdentity]
  exact (sub_le_sub hRate (reciprocal_square_le_reciprocal hm)).trans hReach

end ProphetSecretary.Analysis
