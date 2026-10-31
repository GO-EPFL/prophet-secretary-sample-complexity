import ProphetSecretary.Limiting.HybridExcessState
import ProphetSecretary.Limiting.MappedHybridPotential
import ProphetSecretary.Limiting.BernoulliGeneratorErrorUnder

/-!
# Vanishing mapped reserve residual under original observations

The transformed probability mark law may contain zero. Its original-rate
premium equals the premium of the actual positive excess intensity. This
proved equality calibrates the finite Bernoulli potential without introducing
zero marks into the target hybrid state or deleting any observed history.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n k : ℕ}

theorem RandomizedHybridPolicy.expectedExcessDesignResidual_bounds (π : RandomizedHybridPolicy (n + k))
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) (a : ℝ≥0) (p : unitInterval)
    (hrate : ((B.excessState a).intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let S := B.excessState a
    let κ := normalizedMarkOrZero S.intensity
    let hκ := (B.excessState_markBounds a).mono (fun _ hx => hx.1)
    let Q := finitePoissonDesign S.individuals κ hκ p k
    let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2);
    -C ≤ π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ a w c ∧
      π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ a w c ≤
        (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) + C := by
  let S := B.excessState a
  let κ := normalizedMarkOrZero S.intensity
  let hκ := (B.excessState_markBounds a).mono (fun _ hx => hx.1)
  have hI := B.excessState_markIntegrable a
  have hS := S.individuals.integrable_maximum_of_bounded S.individual_bounded
  let Q := finitePoissonDesign S.individuals κ hκ p k
  have hQ := finitePoissonDesign_integrable_maximum S.individuals κ hκ p k hS hI
  let P := B.individuals.appendZeros k
  let T := (B.appendZeroIndividuals k).individuals.excessOffers a
  let κ₀ : Measure ℝ := B.intensity.normalize
  let hκ₀ := B.normalizedMark_nonnegative hμ
  let κa := Model.excessLaw κ₀ a
  let hκa := Model.excessLaw_nonnegative κ₀ hκ₀ a
  have hIa := Model.excessLaw_integrable κ₀ (B.normalizedMark_integrable hμ) a.property
  have hT := (B.appendZeroIndividuals k).individuals.excessOffers_integrable_maximum
    ((B.appendZeroIndividuals k).individuals.integrable_maximum_of_bounded (B.appendZeroIndividuals k).individual_bounded) a.property
  have hTZ : T = S.individuals.appendZeros k := B.individuals.excessOffers_appendZeros k a.property
  have hgen := π.rule.designResidual_generator_under π.measurable_rule Q T P hQ hT κa hκa hIa
    B.intensity π.seedLaw hw hc
  have herror := π.rule.bernoulliGenerator_integral_error_under π.measurable_rule S.individuals P κ hκ p hS hI
    S.intensity hrate B.intensity π.seedLaw hw hc
  have hpoint (q : HybridWorld (n + k) π.Seed × ℝ) :
      π.rule.potentialGeneratorDrift Q T κa B.intensity w c q =
        π.rule.potentialGeneratorDrift Q (S.individuals.appendZeros k) κ S.intensity w c q := by
    unfold HybridRule.potentialGeneratorDrift
    rw [hTZ]
    congr 1
    unfold HybridRule.poissonPotentialDrift
    split_ifs
    · exact (B.excessState_premiumBalance a hw.le (poissonContinuation_nonnegative Q hQ hw.le hc _ _)).symm
    · rfl
  have he : π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ a w c =
      ∫ q, π.rule.potentialGeneratorDrift Q (S.individuals.appendZeros k) κ S.intensity w c q
        ∂(hybridWorldLaw P B.intensity π.seedLaw).prod Model.Instance.uniformClock := by
    change (∫ v, π.rule.designResidual Q T κa hκa w c v ∂hybridWorldLaw P B.intensity π.seedLaw) = _
    rw [hgen.2.2]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  dsimp only
  change _ ≤ π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ a w c ∧
    π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ a w c ≤ _
  rw [he]
  exact ⟨herror.2.1,herror.2.2⟩

end ProphetSecretary.Limiting
