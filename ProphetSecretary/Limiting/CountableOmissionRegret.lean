import ProphetSecretary.Limiting.CountableTruncationUpper
import ProphetSecretary.Limiting.CountableTruncationLower

/-!
# Quantitative omission bounds for nearly optimal full policies

The scalar weights are fixed. The genuine causal simulator increases duration
and loses at most the omitted maximum in reward. Near optimality bounds both
weighted mean changes and the regret in the actual truncated instance.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def CountableInstance.omissionError (B : CountableInstance) (N : ℕ) (b : ℝ) : ℝ :=
  B.expectedIndividualTailExcessMaximum N+(b-(B.terminal : ℝ))

lemma CountableInstance.omissionError_nonnegative (B : CountableInstance) (N : ℕ)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) : 0 ≤ B.omissionError N b :=
  add_nonneg (B.expectedIndividualTailExcessMaximum_nonnegative N) (sub_nonneg.mpr hb.le)

private lemma mean_tradeoff_bounds {R T R' T' V m w c r : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hT : T ≤ T') (hR : R ≤ R'+m)
    (hUpper : w*R'+c*T' ≤ V) (hNear : V-(w*R+c*T) ≤ r) :
    c*(T'-T) ≤ r+w*m ∧ w*(R'-R) ≤ r := by
  have hReward := mul_le_mul_of_nonneg_left hR hw
  have hDuration := mul_nonneg hc (sub_nonneg.mpr hT)
  constructor
  · nlinarith only [hReward,hUpper,hNear]
  · nlinarith only [hDuration,hUpper,hNear]

lemma RandomizedCountablePolicy.omission_regret_mean_bounds {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {w c r : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hNear : B.optimalScalarValue w c-π.scalarObjective w c ≤ r) :
    let σ := π.simulateOmissions N b
    let C := B.truncation N b hb
    (C.optimalScalarValue w c-σ.scalarObjective C w c ≤ r+w*B.omissionError N b) ∧
      0 ≤ σ.expectedDuration C-π.expectedDuration ∧
      c*(σ.expectedDuration C-π.expectedDuration) ≤ r+w*B.omissionError N b ∧
      w*(σ.expectedReward C-π.expectedReward) ≤ r := by
  let σ := π.simulateOmissions N b
  let C := B.truncation N b hb
  have hComp := π.omission_expected_comparison N hb
  have hUpperJ : σ.scalarObjective C w c ≤ B.optimalScalarValue w c :=
    (C.scalarObjective_le_value σ w c).trans (B.truncation_value_le N hb w c)
  have hUpper : w*σ.expectedReward C+c*σ.expectedDuration C ≤ B.optimalScalarValue w c :=
    (σ.scalarObjective_eq C w c).symm.le.trans hUpperJ
  have hNear' : B.optimalScalarValue w c-(w*π.expectedReward+c*π.expectedDuration) ≤ r := hNear
  have hReward : π.expectedReward ≤ σ.expectedReward C+B.omissionError N b := hComp.2
  have hDuration : π.expectedDuration ≤ σ.expectedDuration C := hComp.1
  have hMeans := mean_tradeoff_bounds hw hc hDuration hReward hUpper hNear'
  have hScalar : π.scalarObjective w c ≤ σ.scalarObjective C w c+w*B.omissionError N b :=
    π.scalarObjective_le_simulateOmissions N hb hw hc
  have hRegret : C.optimalScalarValue w c-σ.scalarObjective C w c ≤ r+w*B.omissionError N b := by
    calc
      _ ≤ B.optimalScalarValue w c-σ.scalarObjective C w c := sub_le_sub_right (B.truncation_value_le N hb w c) _
      _ ≤ (B.optimalScalarValue w c-π.scalarObjective w c)+w*B.omissionError N b := by linarith only [hScalar]
      _ ≤ _ := add_le_add hNear le_rfl
  exact ⟨hRegret,sub_nonneg.mpr hDuration,hMeans.1,hMeans.2⟩

end ProphetSecretary.Limiting
