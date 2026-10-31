import ProphetSecretary.Limiting.OmissionPolicy
import ProphetSecretary.Limiting.PositiveExcessPolicies
import ProphetSecretary.Model.ExcessPositiveTail

/-!
# The causal simulator never selects a dominated retained value

The acceptance gate is part of the constructed simulator, while all low and
zero observations remain in its past history. Its reward is therefore at least
the terminal reserve on every raw execution, including no acceptance.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma simulateOmittedRule_acceptsPositiveExcess (B : CountableInstance) {Seed : Type*}
    (π : CountableRule Seed) (N : ℕ) : (simulateOmittedRule B π N).AcceptsPositiveExcess B.terminal := by
  constructor
  · intro r t i x H ξ h
    apply (Model.excessValueMap_positive_iff B.terminal.property).mpr
    by_contra hn
    change (if (B.terminal : ℝ) < x then
      π.individual r.1.1 t i.val x (augmentIndividualHistory N H r.2.1 r.2.2 t)
        (ξ + omittedCloudPast B r.1.2 t) else false) = true at h
    split_ifs at h with hgate
    exact hn hgate
  · intro r t x H ξ h
    apply (Model.excessValueMap_positive_iff B.terminal.property).mpr
    by_contra hn
    change (if (B.terminal : ℝ) < x then
      π.poisson r.1.1 t x (augmentIndividualHistory N H r.2.1 r.2.2 t)
        (ξ + omittedCloudPast B r.1.2 t) else false) = true at h
    split_ifs at h with hgate
    exact hn hgate

lemma simulateOmittedRule_reward_ge_reserve (B : CountableInstance) {Seed : Type*}
    (π : CountableRule Seed) (N : ℕ) (r : OmissionAux Seed) (x u : Fin N → ℝ) (ω : Configuration) :
    (B.terminal : ℝ) ≤ (simulateOmittedRule B π N).reward B.terminal r x u ω := by
  let ψ := simulateOmittedRule B π N
  by_cases hs : ψ.HasSelection r x u ω
  · obtain ⟨i,hi⟩ := hs
    rw [ψ.reward_eq_of_selection B.terminal r x u ω i hi]
    have hp := ψ.asFinitePolicy_selected_positiveExcess B.terminal
      (simulateOmittedRule_acceptsPositiveExcess B π N) ω.1 r (combinedValues x ω.2) (combinedClocks u ω.2) i hi
    exact ((Model.excessValueMap_positive_iff B.terminal.property).mp hp).le
  · exact le_of_eq (ψ.reward_eq_terminal_of_no_selection B.terminal r x u ω hs).symm

end ProphetSecretary.Limiting
