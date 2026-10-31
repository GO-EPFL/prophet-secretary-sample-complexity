import ProphetSecretary.Limiting.CountableTruncatedRule
import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# Admissible randomized extension of every truncated policy

The auxiliary law is unchanged and independent of the complete online world.
All first N individual observations are retained. No finite-support or threshold
assumption is imposed on the supplied hybrid policy.
-/

open MeasureTheory

namespace ProphetSecretary.Limiting
open CountableInstance

variable {N : ℕ}

noncomputable def RandomizedHybridPolicy.extendToCountable (π : RandomizedHybridPolicy N)
    (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) : RandomizedCountablePolicy B where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := extendTruncatedRule π.rule b
  measurable_rule := extendTruncatedRule_measurable π.rule π.measurable_rule b
  admissible := extendTruncatedRule_admissible B π.rule π.seedLaw hb

end ProphetSecretary.Limiting
