import ProphetSecretary.Limiting.BoundaryCompactWitness
import ProphetSecretary.Limiting.NoRewardCritical

/-!
# Uniform positive reward-boundary slack

Paper correspondence: `lem:boundary-slack` and
`upbound:reward-boundary-slack`. The constant depends only on the common cap
and positive lower bound on the expected maximum, uniformly in the finite
size and all marginal laws. Failure gives normalized finite counterexamples;
actual compact extraction would yield a forbidden reward-critical instance.
-/

open MeasureTheory
open scoped NNReal Classical
namespace ProphetSecretary.Model

theorem bounded_reward_boundary_slack (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu) :
    ∃ d : ℝ, 0<d ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) → mu≤P.expectedMaximum →
      d≤optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum := by
  by_contra hNo
  have hFail : ∀ d : ℝ, 0<d → ∃ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) ∧ mu≤P.expectedMaximum ∧
      optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum<d := by
    intro d hd
    by_contra hMissing
    apply hNo
    refine ⟨d,hd,?_⟩
    intro n P hCap hMean
    by_contra hGap
    exact hMissing ⟨n,P,hCap,hMean,lt_of_not_ge hGap⟩
  obtain ⟨B,_hCap,hMean,hValue,_hZero⟩ :=
    ProphetSecretary.Limiting.exists_critical_countable_of_no_boundary_slack H mu hmu hFail
  exact B.not_normalized_reward_critical hMean hValue

end ProphetSecretary.Model
