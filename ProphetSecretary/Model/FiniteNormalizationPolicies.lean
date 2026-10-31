import ProphetSecretary.Probability.FiniteNormalizationScorePayoffs

/-!
# Fixed-base normalization preserves actual optimizers and canonical scores

The policy transport is a bijection of the full randomized history-dependent
class. Its reward, duration and scalar payoffs are actual expectations under
the scaled laws. The exact canonical callback identity then identifies its
score responses under every perturbed law, with the base means and weights
held fixed.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma RandomizedPolicy.fixedBaseNormalizedPolicy_inverse (π : RandomizedPolicy n) {M : ℝ} (hM : 0<M) :
    (π.fixedBaseNormalizedPolicy M).pullbackValues (M⁻¹*·) (measurable_valueScale M⁻¹)=π := by
  simpa only [fixedBaseNormalizedPolicy,inv_inv] using
    π.pullbackValues_inverse_scale M⁻¹ (inv_ne_zero hM.ne')

lemma RandomizedPolicy.fixedBaseNormalization_expectedReward (π : RandomizedPolicy n) (P : Instance n)
    {M : ℝ} (hM : 0<M) :
    (π.fixedBaseNormalizedPolicy M).expectedReward (P.scale M⁻¹ (inv_nonneg.mpr hM.le))=M⁻¹*π.expectedReward P := by
  rw [(π.fixedBaseNormalizedPolicy M).expectedReward_scale,
    π.fixedBaseNormalizedPolicy_inverse hM]

lemma RandomizedPolicy.fixedBaseNormalization_expectedDuration (π : RandomizedPolicy n) (P : Instance n)
    {M : ℝ} (hM : 0<M) :
    (π.fixedBaseNormalizedPolicy M).expectedDuration (P.scale M⁻¹ (inv_nonneg.mpr hM.le))=π.expectedDuration P := by
  rw [(π.fixedBaseNormalizedPolicy M).expectedDuration_scale,
    π.fixedBaseNormalizedPolicy_inverse hM]

lemma RandomizedPolicy.fixedBaseNormalization_scalarObjective (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) :
    (π.fixedBaseNormalizedPolicy M).scalarObjective (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
      (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c)=
      (finiteNormalizationDenominator M w c)⁻¹*π.scalarObjective P w c := by
  rw [(π.fixedBaseNormalizedPolicy M).scalarObjective_scale P M⁻¹ (inv_nonneg.mpr hM.le) hP,
    π.fixedBaseNormalizedPolicy_inverse hM,finiteNormalization_scaled_reward hM,finiteNormalization_scaled_duration]
  exact π.scalarObjective_smul P hP _ w c

/-- All base optimizers correspond, not only the canonical threshold policies. -/
theorem RandomizedPolicy.fixedBaseNormalization_optimal_iff (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    (π.fixedBaseNormalizedPolicy M).scalarObjective (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
      (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c)=
      optimalScalarValue (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
        (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c) ↔
      π.scalarObjective P w c=optimalScalarValue P w c := by
  rw [π.fixedBaseNormalization_scalarObjective P hP hM,P.fixedBaseNormalization_value hP hM hw hc]
  exact mul_right_inj' (inv_ne_zero (finiteNormalizationDenominator_positive hM hw hc).ne')

lemma Instance.fixedBaseNormalization_canonicalPolicy (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).valuePolicy
      (P.scale_integrable_maximum M⁻¹ (inv_nonneg.mpr hM.le) hP)
      (finiteNormalizationWeights hM hw hc).1.le (finiteNormalizationWeights hM hw hc).2.1=
      (P.valuePolicy hP hw.le hc).fixedBaseNormalizedPolicy M := by
  have hRule := P.fixedBaseNormalization_canonical_rule hP hM hw hc
  unfold Instance.valuePolicy RandomizedPolicy.fixedBaseNormalizedPolicy RandomizedPolicy.pullbackValues
  congr 1

/-- Canonical base policies are identified exactly before evaluating them on
any perturbed law Ptheta. This does not reoptimize at that law. -/
theorem Instance.fixedBaseNormalization_canonical_scores (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) (Ptheta : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) :
    let π := P.valuePolicy hP hw.le hc
    let ρ := (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).valuePolicy
      (P.scale_integrable_maximum M⁻¹ (inv_nonneg.mpr hM.le) hP)
      (finiteNormalizationWeights hM hw hc).1.le (finiteNormalizationWeights hM hw hc).2.1
    ρ.expectedRewardScore (Ptheta.scale M⁻¹ (inv_nonneg.mpr hM.le)) (fixedBaseNormalizedScore M h)=
        M⁻¹*π.expectedRewardScore Ptheta h ∧
      ρ.expectedDurationScore (Ptheta.scale M⁻¹ (inv_nonneg.mpr hM.le)) (fixedBaseNormalizedScore M h)=
        π.expectedDurationScore Ptheta h ∧
      (Ptheta.scale M⁻¹ (inv_nonneg.mpr hM.le)).expectedMaximumScore (fixedBaseNormalizedScore M h)=
        M⁻¹*Ptheta.expectedMaximumScore h := by
  dsimp only
  rw [P.fixedBaseNormalization_canonicalPolicy hP hM hw hc]
  exact ⟨(P.valuePolicy hP hw.le hc).fixedBaseNormalization_rewardScore Ptheta hM h hh,
    (P.valuePolicy hP hw.le hc).fixedBaseNormalization_durationScore Ptheta hM h hh,
    Ptheta.fixedBaseNormalization_maximumScore hM h hh⟩

end ProphetSecretary.Model
