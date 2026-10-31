import ProphetSecretary.Model.FirstMomentIntegrated
import ProphetSecretary.Model.FirstMomentScaleChoice
import ProphetSecretary.Analysis.FirstMomentAbsorption

/-!
# Bounded total first moment near criticality

This is the complete finite-instance theorem `upmom:theorem`. The explicit
positive radius and finite bound depend only on δ and the optimal global
competitive ratio. The proof uses actual value transports, marginal selection
and prophet probabilities, aggregate atom control, the logarithmic tail bound,
and layer-cake integration. No positive lower bound on M is assumed.
-/
open MeasureTheory Set

namespace ProphetSecretary.Model

noncomputable def firstMomentUniformBound (δ : ℝ) : ℝ :=
  17 / 2 + 2 * Real.log (4 * firstMomentLogTailConstant δ)

/-- Explicit-constant form of `upmom:theorem`. -/
theorem Instance.totalFirstMoment_le_of_small_scalarGap {n : ℕ} (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hgap : scalarGap P w c ≤ firstMomentGapRadius δ / (1 + P.positiveCount) ^ 4) :
    P.totalFirstMoment ≤ firstMomentUniformBound δ := by
  let h := Real.sqrt (firstMomentGapRadius δ) / (1 + P.positiveCount) ^ 3
  have hscale := P.firstMoment_scale_choice hδ hwδ hgap
  change 0 < h ∧ h ≤ 1 / 4 ∧ P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant ∧
    firstMomentAtomScaleConstant δ * P.positiveCount * P.firstMomentError δ h w c ≤ 1 / 4 at hscale
  have hi := P.firstMoment_integrated_bound hcap hδ hwδ hcδ hsum hscale.1 hscale.2.1 hscale.2.2.1
  have hS := P.totalFirstMoment_nonnegative
  have hm := mul_le_mul_of_nonneg_right hscale.2.2.2 (by linarith only [hS] : 0 ≤ 1 + P.totalFirstMoment)
  have hscalar : P.totalFirstMoment ≤ (1 + P.totalFirstMoment) / 4 +
      Real.log (firstMomentLogTailConstant δ * (1 + P.totalFirstMoment)) + 4 := by
    nlinarith only [hi,hm]
  exact ProphetSecretary.Analysis.firstMoment_logarithmic_absorption hS
    (firstMomentLogTailConstant_positive δ) hscalar

/-- `upmom:theorem`: uniformity in instance size, marginal laws and scalar
weights follows from the explicit constants preceding this statement. -/
theorem bounded_firstMoment_near_critical {δ : ℝ} (hδ : 0 < δ) :
    ∃ η B : ℝ, 0 < η ∧ ∀ (n : ℕ) (P : Instance n) (w c : ℝ),
      (∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) → δ ≤ w → δ ≤ c → w + c = 1 →
      scalarGap P w c ≤ η / (1 + P.positiveCount) ^ 4 → P.totalFirstMoment ≤ B := by
  refine ⟨firstMomentGapRadius δ,firstMomentUniformBound δ,firstMomentGapRadius_positive hδ,?_⟩
  intro n P w c hcap hw hc hsum hgap
  exact P.totalFirstMoment_le_of_small_scalarGap hcap hδ hw hc hsum hgap

end ProphetSecretary.Model
