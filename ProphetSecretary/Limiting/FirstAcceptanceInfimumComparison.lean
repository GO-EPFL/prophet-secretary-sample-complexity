import ProphetSecretary.Limiting.FirstAcceptanceInfimum

/-!
# Infimum duration under inclusion and relabeling

These analytical comparisons use accepted physical times, without assuming
that a first accepted occurrence is attained on a counterfactual world.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting.FirstAcceptance
variable {Ω Ξ : Type*}

lemma infimumTime_le_of_accepted_times_inclusion
    {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ}
    (hUnitA : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1)
    (hUnitB : ∀ j, B ξ j → v ξ j ∈ Icc (0 : ℝ) 1)
    (hAB : ∀ i, A ω i → ∃ j, B ξ j ∧ u ω i=v ξ j) :
    infimumTime B v ξ ≤ infimumTime A u ω := by
  have hLower := (le_infimumTime_iff hUnitB (infimumTime B v ξ)).mp le_rfl
  apply (le_infimumTime_iff hUnitA _).mpr
  refine ⟨hLower.1,?_⟩
  intro i hi
  obtain ⟨j,hj,hTime⟩ := hAB i hi
  exact (hLower.2 j hj).trans_eq hTime.symm

lemma infimumTime_eq_of_accepted_times_eq
    {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ}
    (hUnitA : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1)
    (hUnitB : ∀ j, B ξ j → v ξ j ∈ Icc (0 : ℝ) 1)
    (hAB : ∀ i, A ω i → ∃ j, B ξ j ∧ u ω i=v ξ j)
    (hBA : ∀ j, B ξ j → ∃ i, A ω i ∧ v ξ j=u ω i) :
    infimumTime A u ω=infimumTime B v ξ :=
  le_antisymm (infimumTime_le_of_accepted_times_inclusion hUnitB hUnitA hBA)
    (infimumTime_le_of_accepted_times_inclusion hUnitA hUnitB hAB)

end ProphetSecretary.Limiting.FirstAcceptance
