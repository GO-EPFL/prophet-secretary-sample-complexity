import ProphetSecretary.Limiting.FinitePotentialPolicy
import ProphetSecretary.Limiting.HybridBranchLaw
import ProphetSecretary.Model.BellmanResidual

/-!
# Finite-branch verification of a common hybrid potential rule

Every branch is evaluated under its actual iid mark law, while the potential
uses zero marginals for anonymous points. Zero-state value invariance removes
the analytical count from the initial potential and from all thresholds.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma appendIID_integrable_maximum (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (hI : Integrable (fun x : ℝ => x) κ) :
    Integrable Model.Instance.maximum (appendIID P κ hκ N).valuesLaw := by
  apply Model.Instance.integrable_maximum
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [appendIID, Fin.addCases_left] using P.integrable_maximum_iff.mp hP i
  | right j =>
    simp only [appendIID, Fin.addCases_right]
    convert! hI using 1

noncomputable def finitePotentialPolicy (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    RandomizedHybridPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := finitePotentialRule Q w c
  measurable_rule := finitePotentialRule_isMeasurable Q hQ hw hc

lemma finitePotentialPolicy_finiteEvaluation (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (N : ℕ) :
    (finitePotentialPolicy Q hQ hw hc).finiteEvaluation N =
      (Q.appendZeros N).valuePolicy (Q.appendZeros_integrable_maximum N hQ) hw hc := by
  unfold RandomizedHybridPolicy.finiteEvaluation finitePotentialPolicy Model.Instance.valuePolicy
  congr 1
  exact finitePotentialRule_adapter Q hQ hw hc N

/-- Branchwise loss decomposition for every admissible hybrid rule. -/
lemma hybrid_branch_residual_identity (π : RandomizedHybridPolicy n) (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x)
    (hI : Integrable (fun x : ℝ => x) κ) (N : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Model.optimalScalarValue Q w c - (π.finiteEvaluation N).scalarObjective (appendIID P κ hκ N) w c =
      (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N) (appendIID P κ hκ N) w c +
      (π.finiteEvaluation N).expectedReachedDesignActionLoss (Q.appendZeros N) (appendIID P κ hκ N) w c := by
  have h := (π.finiteEvaluation N).bellman_residualIdentity_split (Q.appendZeros N) (appendIID P κ hκ N)
    (Q.appendZeros_integrable_maximum N hQ) (appendIID_integrable_maximum P κ hκ N hP hI) hw hc
  rwa [Q.optimalScalarValue_appendZeros N hQ hw.le hc] at h

lemma finitePotentialPolicy_branch_residual_identity (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x)
    (hI : Integrable (fun x : ℝ => x) κ) (N : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let π := finitePotentialPolicy Q hQ hw.le hc
    Model.optimalScalarValue Q w c - (π.finiteEvaluation N).scalarObjective (appendIID P κ hκ N) w c =
      (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N) (appendIID P κ hκ N) w c := by
  dsimp only
  have h := hybrid_branch_residual_identity (finitePotentialPolicy Q hQ hw.le hc) Q P hQ hP κ hκ hI N hw hc
  rw [finitePotentialPolicy_finiteEvaluation Q hQ hw.le hc N,
    Model.Instance.valuePolicy_expectedDesignActionLoss_zero, add_zero] at h
  · rwa [finitePotentialPolicy_finiteEvaluation Q hQ hw.le hc N]
  · exact hw

end ProphetSecretary.Limiting
