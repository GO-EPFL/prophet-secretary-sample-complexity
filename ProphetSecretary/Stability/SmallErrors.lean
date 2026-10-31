import ProphetSecretary.Stability.OutcomeStability

/-!
# Uniform regret radii

The finite outcome-stability modulus gives one positive regret radius for every
prescribed outcome error, uniformly over all instances, weights, and policies.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

theorem finite_small_outcome_errors {α : Type*} (n : α → ℕ)
    (P : ∀ a, Instance (n a)) {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (hbound : ∀ a i, ∀ᵐ x ∂(P a).law i, x ≤ H)
    (htail : ∀ d, 0 < d → ∃ L : ℝ, ∀ a, (P a).tailCount d ≤ L) :
    ∀ ε, 0 < ε → ∃ η, 0 < η ∧
      ∀ a w c, δ ≤ w → δ ≤ c → w + c = 1 → ∀ π : RandomizedPolicy (n a),
      optimalScalarValue (P a) w c - π.scalarObjective (P a) w c ≤ η →
      π.expectedOutcomeError (P a) w c ≤ ε := by
  obtain ⟨ω, _, hmono, _, hlim, herror, _⟩ :=
    finite_outcome_stability n P hH hδ hbound htail
  intro ε hε
  have hevent := Metric.tendsto_nhds.mp hlim ε hε
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨η, hη, hsmall⟩ := (hpos.and hevent).exists
  refine ⟨η, hη, ?_⟩
  intro a w c hw hc hsum π hr
  have hηbound : ω η ≤ ε := by
    rw [Real.dist_eq, sub_zero] at hsmall
    exact (le_abs_self _).trans hsmall.le
  exact (herror a w c hw hc hsum π).trans ((hmono hr).trans hηbound)

end ProphetSecretary.Model
