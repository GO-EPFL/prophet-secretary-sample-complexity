import ProphetSecretary.Limiting.HybridMappedReward
import ProphetSecretary.Limiting.HybridResidualBranchUnder
import ProphetSecretary.Limiting.ExcessFiniteArrays

/-!
# Mapped finite-potential verification with original hybrid observations

The policy executes with original values and original anonymous history. Only
its analytical payoff and target residual laws are mapped to excess values.
Count-mixture integration of the proved finite mapped Bellman identity bounds
all such policies, including policies using observations mapped to zero.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def RandomizedHybridPolicy.expectedExcessDesignResidual (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) (a w c : ℝ) : ℝ :=
  ∫ v, π.rule.designResidual Q (B.individuals.excessOffers a)
    (Model.excessLaw (B.intensity.normalize : Measure ℝ) a)
      (Model.excessLaw_nonnegative _ (B.normalizedMark_nonnegative hμ) a) w c v ∂B.law π.seedLaw

lemma RandomizedHybridPolicy.mappedExcess_branchGap_identity (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) (N : ℕ) :
    let κ : Measure ℝ := B.intensity.normalize
    let κa := Model.excessLaw κ a
    let hκ := B.normalizedMark_nonnegative hμ
    let hκa := Model.excessLaw_nonnegative κ hκ a
    let PN := appendIID B.individuals κ hκ N
    Model.optimalScalarValue Q w c -
      (π.finiteEvaluation N).mappedScalarObjective PN (fun _ => Model.excessValueMap a) w c -
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) (appendIID (B.individuals.excessOffers a) κa hκa N) w c ω.2.2 ω.1 ω.2.1
          ∂PN.worldLaw π.seedLaw =
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.mappedReachedLoss
        (Q.appendZeros N) (fun _ => Model.excessValueMap a) w c ω.2.2 ω.1 ω.2.1 ∂PN.worldLaw π.seedLaw := by
  let κ : Measure ℝ := B.intensity.normalize
  let hκ := B.normalizedMark_nonnegative hμ
  let PN := appendIID B.individuals κ hκ N
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hIκ : Integrable (fun x : ℝ => x) κ := by convert! B.normalizedMark_integrable hμ using 1
  have hPN := appendIID_integrable_maximum B.individuals κ hκ N hP hIκ
  have hm := (π.finiteEvaluation N).mapped_bellman_performance (Q.appendZeros N) PN
    (Q.appendZeros_integrable_maximum N hQ) hPN (fun _ => Model.excessValueMap a)
      (fun _ => Model.measurable_excessValueMap a)
      (fun i => (PN.nonnegative i).mono fun _ hx => Model.excessValueMap_nonnegative hx)
        ha hw hc (fun _ x => Model.excessValueMap_displacement ha x)
  have htarget : PN.mapValues (fun _ => Model.excessValueMap a) (fun _ => Model.measurable_excessValueMap a)
      (fun i => (PN.nonnegative i).mono fun _ hx => Model.excessValueMap_nonnegative hx) =
      appendIID (B.individuals.excessOffers a) (Model.excessLaw κ a) (Model.excessLaw_nonnegative κ hκ a) N :=
    excessOffers_appendIID B.individuals κ hκ N a
  have he := hm.2
  rw [Q.optimalScalarValue_appendZeros N hQ hw.le hc,htarget] at he
  let TN := appendIID (B.individuals.excessOffers a) (Model.excessLaw κ a) (Model.excessLaw_nonnegative κ hκ a) N
  change Model.optimalScalarValue Q w c - (π.finiteEvaluation N).mappedScalarObjective PN
    (fun _ => Model.excessValueMap a) w c =
      (∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.mappedReachedLoss (Q.appendZeros N)
        (fun _ => Model.excessValueMap a) w c ω.2.2 ω.1 ω.2.1 ∂PN.worldLaw π.seedLaw) +
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) TN w c ω.2.2 ω.1 ω.2.1 ∂PN.worldLaw π.seedLaw at he
  dsimp only
  change Model.optimalScalarValue Q w c - (π.finiteEvaluation N).mappedScalarObjective PN
    (fun _ => Model.excessValueMap a) w c -
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) TN w c ω.2.2 ω.1 ω.2.1 ∂PN.worldLaw π.seedLaw =
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.mappedReachedLoss
        (Q.appendZeros N) (fun _ => Model.excessValueMap a) w c ω.2.2 ω.1 ω.2.1 ∂PN.worldLaw π.seedLaw
  linarith only [he]

lemma RandomizedHybridPolicy.mappedExcess_branchGap_nonnegative (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) (N : ℕ) :
    let κ : Measure ℝ := B.intensity.normalize
    let κa := Model.excessLaw κ a
    let hκ := B.normalizedMark_nonnegative hμ
    let hκa := Model.excessLaw_nonnegative κ hκ a
    let PN := appendIID B.individuals κ hκ N
    0 ≤ Model.optimalScalarValue Q w c -
      (π.finiteEvaluation N).mappedScalarObjective PN (fun _ => Model.excessValueMap a) w c -
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) (appendIID (B.individuals.excessOffers a) κa hκa N) w c ω.2.2 ω.1 ω.2.1
          ∂PN.worldLaw π.seedLaw := by
  have h := π.mappedExcess_branchGap_identity Q hQ B hμ ha hw hc N
  dsimp only at h ⊢
  rw [h]
  exact integral_nonneg fun ω => (π.finiteEvaluation N).rule.mappedReachedLoss_nonnegative
    (Q.appendZeros N) (fun _ => Model.excessValueMap a) w c ω.2.2 ω.1 ω.2.1

/-- An all-policy upper verification with analytically transformed target laws.
It supplies no transformed future observations to the competing rule. -/
theorem RandomizedHybridPolicy.mappedExcessScalarObjective_le_finitePotential (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    π.mappedExcessScalarObjective B a w c ≤ Model.optimalScalarValue Q w c -
      π.expectedExcessDesignResidual Q B hμ a w c := by
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
  have hsum : HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      (Model.optimalScalarValue Q w c - (π.finiteEvaluation N).mappedScalarObjective
        (appendIID B.individuals κ hκ N) (fun _ => Model.excessValueMap a) w c -
        ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
          (Q.appendZeros N) (appendIID T κa hκa N) w c ω.2.2 ω.1 ω.2.1
            ∂(appendIID B.individuals κ hκ N).worldLaw π.seedLaw))
      (Model.optimalScalarValue Q w c - π.mappedExcessScalarObjective B a w c -
        π.expectedExcessDesignResidual Q B hμ a w c) := by
    convert! hs using 1
    · funext N
      ring
    · simp only [one_mul]
      rfl
  have hnn : 0 ≤ Model.optimalScalarValue Q w c - π.mappedExcessScalarObjective B a w c -
      π.expectedExcessDesignResidual Q B hμ a w c := by
    rw [← hsum.tsum_eq]
    apply tsum_nonneg
    intro N
    exact mul_nonneg (by unfold poissonWeight; positivity)
      (π.mappedExcess_branchGap_nonnegative Q hQ B hμ ha hw hc N)
  linarith only [hnn]

end ProphetSecretary.Limiting
