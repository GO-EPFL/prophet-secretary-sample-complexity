import ProphetSecretary.Model.FiniteBaseNormalization

/-!
# Canonical decisions under fixed-base normalization

Positive value scaling preserves each unseen-identity state and all observed
zero identities. The actual child optimal values scale by the same constant,
so every threshold decision, including equality, is preserved on every raw
history. This is stronger than equality of optimized scalar values alone.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma unseen_mapHistoryValues (g : ℝ → ℝ) (H : History n) :
    unseen (mapHistoryValues g H)=unseen H := by
  ext i
  simp only [unseen,Finset.mem_filter,Finset.mem_univ,true_and,mapHistoryValues]
  cases H i <;> simp [mapObservationValues]

lemma Instance.restrictTo_scale (P : Instance n) (a : ℝ) (ha : 0≤a) (A : Finset (Fin n)) :
    (P.scale a ha).restrictTo A=(P.restrictTo A).scale a ha := by
  apply Instance.eq_of_law_eq
  rfl

lemma Instance.fixedBaseNormalization_continuation (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) (A : Finset (Fin n)) (u : ℝ) (hu : 0≤u) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).continuationValue A u
      (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c)=
      (finiteNormalizationDenominator M w c)⁻¹*P.continuationValue A u w c := by
  have hWeights := finiteNormalizationWeights hM hw hc
  unfold Instance.continuationValue
  rw [P.restrictTo_scale,optimalScalarValue_scale (P.restrictTo A) M⁻¹ (inv_pos.mpr hM)
    (P.restrictTo_integrable_maximum A hP) hWeights.1.le (mul_nonneg hWeights.2.1 hu),
    finiteNormalization_scaled_reward hM]
  have hC : finiteNormalizationDurationWeight M w c*u=(finiteNormalizationDenominator M w c)⁻¹*(c*u) := by
    rw [finiteNormalization_scaled_duration]
    ring
  rw [hC]
  exact optimalScalarValue_smul (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
    (inv_nonneg.mpr (finiteNormalizationDenominator_positive hM hw hc).le) hw.le (mul_nonneg hc hu)

lemma Instance.fixedBaseNormalization_threshold (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).valueThreshold
      (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c) A t i=
      M⁻¹*P.valueThreshold w c A t i := by
  unfold Instance.valueThreshold
  rw [P.fixedBaseNormalization_continuation hP hM hw hc (A.erase i) _ (le_max_left _ _)]
  unfold finiteNormalizationRewardWeight finiteNormalizationDenominator
  field_simp [hM.ne',hw.ne',show w*M+c≠0 from (finiteNormalizationDenominator_positive hM hw hc).ne']

/-- The new canonical callback is exactly the old callback with every displayed
value multiplied by the fixed unperturbed benchmark M. -/
lemma Instance.fixedBaseNormalization_canonical_rule (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {M w c : ℝ}
    (hM : 0<M) (hw : 0<w) (hc : 0≤c) :
    ((P.scale M⁻¹ (inv_nonneg.mpr hM.le)).valuePolicy
      (P.scale_integrable_maximum M⁻¹ (inv_nonneg.mpr hM.le) hP)
      (finiteNormalizationWeights hM hw hc).1.le (finiteNormalizationWeights hM hw hc).2.1).rule=
      (P.valuePolicy hP hw.le hc).rule.pullbackValues (M*·) := by
  apply congrArg Policy.mk
  funext r t i x H
  change decide ((P.scale M⁻¹ (inv_nonneg.mpr hM.le)).valueThreshold
    (finiteNormalizationRewardWeight M w c) (finiteNormalizationDurationWeight M w c) (unseen H) t i≤x)=
      decide (P.valueThreshold w c (unseen (mapHistoryValues (M*·) H)) t i≤M*x)
  rw [unseen_mapHistoryValues,P.fixedBaseNormalization_threshold hP hM hw hc]
  have hIff : M⁻¹*P.valueThreshold w c (unseen H) t i≤x ↔ P.valueThreshold w c (unseen H) t i≤M*x := by
    rw [←div_eq_inv_mul,div_le_iff₀ hM,mul_comm x M]
  simp only [hIff]

end ProphetSecretary.Model
