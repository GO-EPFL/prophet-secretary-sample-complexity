import ProphetSecretary.Limiting.CountableSelectedTagBounds
import ProphetSecretary.Limiting.CountableOutcomeStability

/-!
# Selected-occurrence stability in full limiting instances

This is the limiting-instance assertion of `cor:selected-occurrence`.
A common bounded measurable tag vanishes below a fixed positive value.
The modulus is uniform over the indicated family and arbitrary competing
policies, and includes independent auxiliary tags revealed at an occurrence.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting
open CountableInstance

theorem countable_selectedOccurrence_stability_with_profile {α : Type*} (B : α → CountableInstance)
    {H δ D b : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) (hD : 0 ≤ D) (hb : 0 < b)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → ((B a).totalTailMass d).toReal ≤ L d) :
    ∃ ψ : ℝ → ℝ, (∀ r, 0 ≤ ψ r) ∧ Monotone ψ ∧ ψ 0=0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a w c, δ ≤ w → δ ≤ c → w+c=1 → ∀ π : RandomizedCountablePolicy (B a),
        ∀ tag : CountableTags π.Seed, tag.IsMeasurable →
        (∀ᵐ v ∂(B a).completeWorldLaw π.seedLaw, ∀ i, |tag v i| ≤ D) →
        (∀ᵐ v ∂(B a).completeWorldLaw π.seedLaw, ∀ i, codeValue v i < b → tag v i=0) →
        π.expectedSelectedTagError w c tag ≤ ψ ((B a).optimalScalarValue w c-π.scalarObjective w c) := by
  obtain ⟨Ω,hΩ,hMono,hZero,hLimit,hError⟩ :=
    countable_outcome_stability_with_profile B hH hδ ha hCap L hL hTail
  let ψ := fun r => Model.selectedTagErrorBound D b (1+L (b/2)) (Ω r)
  refine ⟨ψ,(fun r => Model.selectedTagErrorBound_nonnegative hD hb (hΩ r).1),
    (Model.selectedTagErrorBound_monotone hD hb).comp hMono,?_,?_,?_⟩
  · dsimp only [ψ]
    rw [hZero,Model.selectedTagErrorBound_zero]
  · exact Model.selectedTagErrorBound_tendsto_zero hLimit D b (1+L (b/2))
  · intro a w c hw hc hSum π tag hTag hBound hTagZero
    exact π.selectedTag_stability_of_outcome_bound (ha a) (hδ.le.trans hw) (hδ.le.trans hc) hD hb
      (hTail a (b/2) (half_pos hb)) (hError a w c hw hc hSum π) tag hTag hBound hTagZero

theorem countable_selectedOccurrence_stability_fixed_weights {α : Type*} (B : α → CountableInstance)
    {H w c D b : ℝ} (hH : 0 ≤ H) (hw : 0 < w) (hc : 0 < c) (hD : 0 ≤ D) (hb : 0 < b)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → ((B a).totalTailMass d).toReal ≤ L d) :
    ∃ ψ : ℝ → ℝ, (∀ r, 0 ≤ ψ r) ∧ Monotone ψ ∧ ψ 0=0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a (π : RandomizedCountablePolicy (B a)),
        ∀ tag : CountableTags π.Seed, tag.IsMeasurable →
        (∀ᵐ v ∂(B a).completeWorldLaw π.seedLaw, ∀ i, |tag v i| ≤ D) →
        (∀ᵐ v ∂(B a).completeWorldLaw π.seedLaw, ∀ i, codeValue v i < b → tag v i=0) →
        π.expectedSelectedTagError w c tag ≤ ψ ((B a).optimalScalarValue w c-π.scalarObjective w c) := by
  obtain ⟨Ω,hΩ,hMono,hZero,hLimit,hError⟩ :=
    countable_outcome_stability_fixed_weights B hH hw hc ha hCap L hL hTail
  let ψ := fun r => Model.selectedTagErrorBound D b (1+L (b/2)) (Ω r)
  refine ⟨ψ,(fun r => Model.selectedTagErrorBound_nonnegative hD hb (hΩ r).1),
    (Model.selectedTagErrorBound_monotone hD hb).comp hMono,?_,?_,?_⟩
  · dsimp only [ψ]
    rw [hZero,Model.selectedTagErrorBound_zero]
  · exact Model.selectedTagErrorBound_tendsto_zero hLimit D b (1+L (b/2))
  · intro a π tag hTag hBound hTagZero
    exact π.selectedTag_stability_of_outcome_bound (ha a) hw.le hc.le hD hb
      (hTail a (b/2) (half_pos hb)) (hError a π) tag hTag hBound hTagZero

end ProphetSecretary.Limiting
