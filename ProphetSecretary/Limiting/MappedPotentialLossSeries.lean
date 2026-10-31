import ProphetSecretary.Limiting.MappedHybridPotential

/-!
# Count-mixture series of actual mapped Bellman losses

The same fixed shared hybrid policy is evaluated on every count branch. The
series sums its genuine mapped action losses, not count-dependent optimized
values. Its sum is the finite-potential gap minus the actual target residual.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma RandomizedHybridPolicy.hasSum_mappedExcess_loss (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.mappedReachedLoss (Q.appendZeros N)
        (fun _ => Model.excessValueMap a) w c ω.2.2 ω.1 ω.2.1
          ∂(appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N).worldLaw π.seedLaw)
      (Model.optimalScalarValue Q w c - π.mappedExcessScalarObjective B a w c -
        π.expectedExcessDesignResidual Q B hμ a w c) := by
  let κ : Measure ℝ := B.intensity.normalize
  let hκ := B.normalizedMark_nonnegative hμ
  let T := B.individuals.excessOffers a
  let κa := Model.excessLaw κ a
  let hκa := Model.excessLaw_nonnegative κ hκ a
  have hT := B.individuals.excessOffers_integrable_maximum
    (B.individuals.integrable_maximum_of_bounded B.individual_bounded) ha
  have hIa := Model.excessLaw_integrable κ (B.normalizedMark_integrable hμ) ha
  have hJ := π.hasSum_mappedExcess_branches B hμ ha w c
  have hD := π.hasSum_designResidual_under Q T hQ hT κa hκa hIa B hμ hw hc
  have hW : HasSum (poissonWeight B.intensity.mass) 1 := by
    convert! hasSum_one_poissonMeasure B.intensity.mass using 1
  have hs := ((hW.mul_right (Model.optimalScalarValue Q w c)).sub hJ).sub hD
  convert! hs using 1
  · funext N
    have he := π.mappedExcess_branchGap_identity Q hQ B hμ ha hw hc N
    dsimp only at he
    rw [← he]
    ring
  · simp only [one_mul]
    rfl

end ProphetSecretary.Limiting
