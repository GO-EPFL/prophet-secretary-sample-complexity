import ProphetSecretary.Limiting.HybridValueTieNull
import ProphetSecretary.Limiting.HybridZeroAppendValue

/-!
# The measurable actual-continuation threshold policy

This bundles the checked observable callbacks with the independent trivial
seed law. Its scalar performance is an actual policy payoff; identifying that
payoff with the full-policy supremum requires the verification theorem.
Appending virtual zero identities uses the proved causal ignore-extra map.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.valueThresholdPolicy (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : RandomizedHybridPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := B.valueRule w c
  measurable_rule := B.valueRule_isMeasurable hw hc

lemma FiniteIntensityHybridInstance.valueThresholdPolicy_scalar_le (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.valueThresholdPolicy hw hc).scalarObjective B w c ≤ B.optimalScalarValue w c :=
  B.scalarObjective_le_value _ w c

lemma FiniteIntensityHybridInstance.valueThresholdPolicy_ignore_zero_scalar (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : ℕ) :
    ((B.valueThresholdPolicy hw hc).ignoreIndividualExtras q).scalarObjective (B.appendZeroIndividuals q) w c =
      (B.valueThresholdPolicy hw hc).scalarObjective B w c :=
  (B.valueThresholdPolicy hw hc).scalarObjective_ignoreIndividualExtras B q ha w c

end ProphetSecretary.Limiting
