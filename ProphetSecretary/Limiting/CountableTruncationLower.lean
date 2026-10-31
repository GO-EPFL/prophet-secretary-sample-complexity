import ProphetSecretary.Limiting.HybridObserverPayoff

/-!
# Every truncated policy is available on the actual full instance

The extension preserves expected reward and duration under the same independent
auxiliary law. The proof transports actual observer payoffs, rather than
identifying value limits or allowing a policy to observe generation labels.
-/

open MeasureTheory

namespace ProphetSecretary.Limiting
open CountableInstance

variable {N : ℕ}

lemma RandomizedHybridPolicy.extendToCountable_expectedReward (π : RandomizedHybridPolicy N)
    (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    (π.extendToCountable B hb).expectedReward = π.expectedReward (B.truncation N b hb) := by
  rw [π.extended_expectedReward_observable B hb]
  exact π.expectedReward_observable (B.truncation N b hb)

lemma RandomizedHybridPolicy.extendToCountable_expectedDuration (π : RandomizedHybridPolicy N)
    (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    (π.extendToCountable B hb).expectedDuration = π.expectedDuration (B.truncation N b hb) := by
  rw [π.extended_expectedDuration_observable B hb]
  exact π.expectedDuration_observable (B.truncation N b hb)

lemma RandomizedHybridPolicy.extendToCountable_scalarObjective (π : RandomizedHybridPolicy N)
    (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) (w c : ℝ) :
    (π.extendToCountable B hb).scalarObjective w c = π.scalarObjective (B.truncation N b hb) w c := by
  rw [RandomizedCountablePolicy.scalarObjective,π.scalarObjective_eq,
    π.extendToCountable_expectedReward B hb,π.extendToCountable_expectedDuration B hb]

lemma CountableInstance.truncation_value_le (B : CountableInstance) (N : ℕ) {b : ℝ}
    (hb : (B.terminal : ℝ) < b) (w c : ℝ) :
    (B.truncation N b hb).optimalScalarValue w c ≤ B.optimalScalarValue w c := by
  apply csSup_le ((B.truncation N b hb).scalarPayoffs_nonempty w c)
  rintro _ ⟨π,rfl⟩
  change π.scalarObjective (B.truncation N b hb) w c ≤ B.optimalScalarValue w c
  rw [← π.extendToCountable_scalarObjective B hb w c]
  exact B.scalarObjective_le_value (π.extendToCountable B hb) w c

end ProphetSecretary.Limiting
