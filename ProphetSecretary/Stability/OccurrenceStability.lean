import ProphetSecretary.Stability.OutcomeStability
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# Uniform stability of the selected positive occurrence

This is the finite-family part of `cor:selected-occurrence`. Tags are common to
the two coupled executions. Allowing measurable tags on the complete coupled
world includes bounded value-dependent tags and independent auxiliary tags.
The conclusion does not supply these analytical tags as observations to a policy.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

/-- The modulus is uniform in the instance size, normalized interior weights,
competing policy, and common bounded tags supported above the positive level. -/
theorem finite_selectedOccurrence_stability {α : Type*} (n : α → ℕ)
    (P : ∀ a, Instance (n a)) {H δ B b : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (hbound : ∀ a i, ∀ᵐ x ∂(P a).law i, x ≤ H)
    (htail : ∀ d, 0 < d → ∃ L : ℝ, ∀ a, (P a).tailCount d ≤ L)
    (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ ψ : ℝ → ℝ, (∀ t, 0 ≤ ψ t) ∧ Monotone ψ ∧ ψ 0 = 0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a w c, δ ≤ w → δ ≤ c → w + c = 1 → ∀ π : RandomizedPolicy (n a),
      ∀ tag : π.World → Fin (n a) → ℝ, (∀ i, Measurable fun ω => tag ω i) →
      (∀ᵐ ω ∂(P a).worldLaw π.seedLaw, ∀ i, |tag ω i| ≤ B) →
      (∀ᵐ ω ∂(P a).worldLaw π.seedLaw, ∀ i, ω.1 i < b → tag ω i = 0) →
      (∫ ω : π.World, |π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (tag ω) -
        ((P a).canonicalRule w c).selectedTag () ω.1 ω.2.1 (tag ω)|
          ∂(P a).worldLaw π.seedLaw) ≤
        ψ (optimalScalarValue (P a) w c - π.scalarObjective (P a) w c) := by
  obtain ⟨ω, hω, hmono, hzero, hlim, herror, _⟩ :=
    finite_outcome_stability n P hH hδ hbound htail
  obtain ⟨L, hL⟩ := htail (b / 2) (by positivity)
  let ψ : ℝ → ℝ := fun r => selectedTagErrorBound B b L (ω r)
  refine ⟨ψ, ?_, (selectedTagErrorBound_monotone hB hb).comp hmono, ?_, ?_, ?_⟩
  · intro t
    exact selectedTagErrorBound_nonnegative hB hb (hω t).1
  · dsimp [ψ]
    rw [hzero, selectedTagErrorBound_zero]
  · exact selectedTagErrorBound_tendsto_zero hlim B b L
  · intro a w c hw hc hsum π tag htag htagB htagzero
    exact π.selectedTag_stability_of_outcome_bound (P a)
      ((P a).integrable_maximum_of_bounded (hbound a))
      (hδ.trans_le hw) (hδ.le.trans hc) hB hb (hL a)
      (herror a w c hw hc hsum π) tag htag htagB htagzero

end ProphetSecretary.Model
