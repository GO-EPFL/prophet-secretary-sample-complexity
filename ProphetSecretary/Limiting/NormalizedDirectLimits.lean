import ProphetSecretary.Limiting.NormalizedDirectBase
import ProphetSecretary.Limiting.NoReserve

/-!
# Critical gaps of the actual normalized direct bases

Every fixed finite tail shift preserves the proved direct maximum and value
limits. The normalizing denominator tends to one. Its exact gap identity
therefore gives normalized gaps tending to zero at the new interior weights,
without any total first-moment hypothesis.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

lemma directShift_tendsto (J : ℕ) : Tendsto (fun m : ℕ => m+J) atTop atTop :=
  tendsto_atTop_mono (fun m => show m≤m+J by omega) tendsto_id

lemma shiftedDirectBase_expectedMaximum_tendsto (B : CountableInstance) (hZero : B.terminal=0) (J : ℕ) :
    Tendsto (fun m => (B.shiftedDirectBase hZero J m).expectedMaximum) atTop (𝓝 B.expectedMaximum) := by
  have h := (B.directFiniteApproximation_expectedMaximum_tendsto hZero).comp (directShift_tendsto J)
  change Tendsto (fun m => (B.shiftedDirectBase hZero J m).expectedMaximum) atTop (𝓝 B.expectedMaximum) at h
  exact h

lemma shiftedDirectMean_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) (J : ℕ) :
    Tendsto (B.shiftedDirectMean hZero J) atTop (𝓝 (1 : ℝ)) := by
  change Tendsto (fun m => (B.shiftedDirectBase hZero J m).expectedMaximum) atTop (𝓝 (1 : ℝ))
  simpa only [hMean] using B.shiftedDirectBase_expectedMaximum_tendsto hZero J

lemma shiftedDirectBase_value_tendsto (B : CountableInstance) (hZero : B.terminal=0) (J : ℕ)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => Model.optimalScalarValue (B.shiftedDirectBase hZero J m) w c) atTop (𝓝 (B.optimalScalarValue w c)) := by
  have h := (B.directFiniteApproximation_value_tendsto hZero hw hc).comp (directShift_tendsto J)
  change Tendsto (fun m => Model.optimalScalarValue (B.shiftedDirectBase hZero J m) w c) atTop (𝓝 (B.optimalScalarValue w c)) at h
  exact h

lemma shiftedDirectBase_gap_tendsto (B : CountableInstance) (hZero : B.terminal=0) (J : ℕ)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) (hCritical : B.IsCritical w c) :
    Tendsto (fun m => Model.scalarGap (B.shiftedDirectBase hZero J m) w c) atTop (𝓝 (0 : ℝ)) := by
  have h := (B.shiftedDirectBase_value_tendsto hZero J hw hc).sub
    ((((B.shiftedDirectBase_expectedMaximum_tendsto hZero J).const_mul w).add_const c).const_mul optimalCompetitiveRatio)
  change Tendsto (fun m => Model.scalarGap (B.shiftedDirectBase hZero J m) w c) atTop (𝓝 (B.scalarGap w c)) at h
  rwa [hCritical.2] at h

lemma normalizedDirectWeights_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) (J : ℕ) {w c : ℝ} (hSum : w+c=1) :
    Tendsto (B.normalizedDirectRewardWeight hZero J w c) atTop (𝓝 w) ∧
      Tendsto (B.normalizedDirectDurationWeight hZero J w c) atTop (𝓝 c) :=
  fixedBaseNormalization_weights_tendsto (B.shiftedDirectMean hZero J) (B.shiftedDirectMean_tendsto hZero hMean J) hSum

lemma normalizedDirectBase_gap_eq (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) (m : ℕ) :
    normalizedScalarGap (B.normalizedDirectBase hZero hMean hJ m) (B.normalizedDirectRewardWeight hZero J w c m)=
      (finiteNormalizationDenominator (B.shiftedDirectMean hZero J m) w c)⁻¹*
        Model.scalarGap (B.shiftedDirectBase hZero J m) w c := by
  have hWeights := B.normalizedDirectWeights_sum hZero hMean hJ hw hc m
  have hC : B.normalizedDirectDurationWeight hZero J w c m=1-B.normalizedDirectRewardWeight hZero J w c m := by
    linarith only [hWeights]
  unfold normalizedScalarGap
  rw [←hC]
  exact (B.shiftedDirectBase hZero J m).fixedBaseNormalization_gap
    ((B.shiftedDirectBase hZero J m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero (m+J)))
    (B.shiftedDirectMean_positive hZero hMean hJ m) hw hc

/-- The base-gap requirement of `prop:critical-input` for actual normalized
finite laws and the explicit normalized weights. -/
theorem normalizedDirectBase_gap_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hCritical : B.IsCritical w c) :
    Tendsto (fun m => normalizedScalarGap (B.normalizedDirectBase hZero hMean hJ m)
      (B.normalizedDirectRewardWeight hZero J w c m)) atTop (𝓝 (0 : ℝ)) := by
  have hD := ((B.shiftedDirectMean_tendsto hZero hMean J).const_mul w).add_const c
  change Tendsto (fun m => finiteNormalizationDenominator (B.shiftedDirectMean hZero J m) w c)
    atTop (𝓝 (w*1+c)) at hD
  have hD1 : Tendsto (fun m => finiteNormalizationDenominator (B.shiftedDirectMean hZero J m) w c)
      atTop (𝓝 (1 : ℝ)) := by simpa only [mul_one,hSum] using hD
  have hGap := B.shiftedDirectBase_gap_tendsto hZero J hw.le hc.le hCritical
  have h := (hD1.inv₀ (by norm_num : (1 : ℝ)≠0)).mul hGap
  change Tendsto (fun m => (finiteNormalizationDenominator (B.shiftedDirectMean hZero J m) w c)⁻¹*
    Model.scalarGap (B.shiftedDirectBase hZero J m) w c) atTop (𝓝 ((1 : ℝ)⁻¹*0)) at h
  simp only [inv_one,mul_zero] at h
  simp_rw [B.normalizedDirectBase_gap_eq hZero hMean hJ hw hc.le]
  exact h

lemma normalizedDirectWeights_quarter (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hSum : w+c=1)
    (hQuarterW : 1/4≤w) (hQuarterC : 1/4≤c) (m : ℕ) :
    B.normalizedDirectRewardWeight hZero J w c m∈Icc (1/16 : ℝ) (1-1/16) := by
  have h := B.normalizedDirectWeights_interior hZero hMean hJ hw hc hSum m
  have hMin : (1/4 : ℝ)≤min w c := le_min hQuarterW hQuarterC
  constructor <;> linarith only [h.1,h.2,hMin]

end ProphetSecretary.Limiting.CountableInstance
