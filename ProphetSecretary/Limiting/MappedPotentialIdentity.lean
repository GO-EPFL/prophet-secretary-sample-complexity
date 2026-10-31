import ProphetSecretary.Limiting.MappedPotentialLossSeries
import ProphetSecretary.Limiting.MappedFinitePotentialPolicy

/-!
# Exact mapped residual identity for the shared positive potential rule

All count branches have zero mapped action loss by their proved finite
adapters. The count-mixture series therefore gives equality, while arbitrary
competing rules retain the upper inequality in MappedHybridPotential.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

theorem mappedPositivePotentialPolicy_residual_identity (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity ≠ 0) {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    let π := mappedPositivePotentialPolicy Q hQ a hw.le hc
    Model.optimalScalarValue Q w c - π.mappedExcessScalarObjective B a w c =
      π.expectedExcessDesignResidual Q B hμ a w c := by
  let π := mappedPositivePotentialPolicy Q hQ a hw.le hc
  have hs := π.hasSum_mappedExcess_loss Q hQ B hμ ha hw hc
  have hz (N : ℕ) : (∫ ω : (π.finiteEvaluation N).World,
      (π.finiteEvaluation N).rule.mappedReachedLoss (Q.appendZeros N) (fun _ => Model.excessValueMap a)
        w c ω.2.2 ω.1 ω.2.1
          ∂(appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N).worldLaw π.seedLaw) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun ω => mappedPositivePotentialRule_branch_loss_zero Q hQ a hw hc N ω.2.2 ω.1 ω.2.1
  have h := hs.tsum_eq
  simp only [hz,mul_zero,tsum_zero] at h
  dsimp only
  linarith only [h]

end ProphetSecretary.Limiting
