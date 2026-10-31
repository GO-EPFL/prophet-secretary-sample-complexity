import ProphetSecretary.Model.CanonicalNormalization
import ProphetSecretary.Model.Scaling
import ProphetSecretary.Reach.Robust

/-!
# Fixed-base finite normalization

M is the unperturbed benchmark and is held fixed throughout any law family.
Offers are divided by M, while both scalar payoffs are divided by wM+c.
The identities below hold for every perturbed law P with these same constants;
no parameter-dependent benchmark is differentiated.
Paper correspondence: `eq:finite-normalization`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model

noncomputable def finiteNormalizationDenominator (M w c : ℝ) : ℝ := w*M+c
noncomputable def finiteNormalizationRewardWeight (M w c : ℝ) : ℝ := w*M/(w*M+c)
noncomputable def finiteNormalizationDurationWeight (M w c : ℝ) : ℝ := c/(w*M+c)

lemma finiteNormalizationDenominator_positive {M w c : ℝ} (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    0<finiteNormalizationDenominator M w c := (mul_pos hw hM).trans_le (le_add_of_nonneg_right hc)

lemma finiteNormalizationWeights {M w c : ℝ} (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    0<finiteNormalizationRewardWeight M w c ∧ 0≤finiteNormalizationDurationWeight M w c ∧
      finiteNormalizationRewardWeight M w c+finiteNormalizationDurationWeight M w c=1 := by
  have hD := finiteNormalizationDenominator_positive hM hw hc
  refine ⟨div_pos (mul_pos hw hM) hD,div_nonneg hc hD.le,?_⟩
  unfold finiteNormalizationRewardWeight finiteNormalizationDurationWeight
  rw [←add_div,div_self (show w*M+c≠0 from hD.ne')]

lemma finiteNormalization_scaled_reward {M w c : ℝ} (hM : 0<M) :
    M⁻¹*finiteNormalizationRewardWeight M w c=(finiteNormalizationDenominator M w c)⁻¹*w := by
  unfold finiteNormalizationRewardWeight finiteNormalizationDenominator
  field_simp

lemma finiteNormalization_scaled_duration (M w c : ℝ) :
    finiteNormalizationDurationWeight M w c=(finiteNormalizationDenominator M w c)⁻¹*c := by
  unfold finiteNormalizationDurationWeight finiteNormalizationDenominator
  ring

lemma Instance.fixedBaseNormalization_value {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    optimalScalarValue (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
      (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c)=
      (finiteNormalizationDenominator M w c)⁻¹*optimalScalarValue P w c := by
  have hWeights := finiteNormalizationWeights hM hw hc
  rw [optimalScalarValue_scale P M⁻¹ (inv_pos.mpr hM) hP hWeights.1.le hWeights.2.1,
    finiteNormalization_scaled_reward hM,finiteNormalization_scaled_duration]
  exact optimalScalarValue_smul P hP (inv_nonneg.mpr (finiteNormalizationDenominator_positive hM hw hc).le) hw.le hc

lemma Instance.fixedBaseNormalization_gap {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    scalarGap (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
      (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c)=
      (finiteNormalizationDenominator M w c)⁻¹*scalarGap P w c := by
  unfold scalarGap
  rw [P.fixedBaseNormalization_value hP hM hw hc,P.scale_expectedMaximum]
  have hW := finiteNormalization_scaled_reward (w:=w) (c:=c) hM
  have hC := finiteNormalization_scaled_duration M w c
  rw [hC]
  calc
    _ = (finiteNormalizationDenominator M w c)⁻¹*optimalScalarValue P w c-
        optimalCompetitiveRatio*((finiteNormalizationDenominator M w c)⁻¹*w*P.expectedMaximum+
          (finiteNormalizationDenominator M w c)⁻¹*c) := by
      congr 2
      congr 1
      calc
        finiteNormalizationRewardWeight M w c*(M⁻¹*P.expectedMaximum)=
            (M⁻¹*finiteNormalizationRewardWeight M w c)*P.expectedMaximum := by ring
        _ = _ := by rw [hW]
    _ = _ := by ring

lemma Instance.fixedBaseNormalization_mean {n : ℕ} (P : Instance n) (hM : 0<P.expectedMaximum) :
    (P.scale P.expectedMaximum⁻¹ (inv_nonneg.mpr hM.le)).expectedMaximum=1 := by
  rw [P.scale_expectedMaximum,inv_mul_cancel₀ hM.ne']

end ProphetSecretary.Model
