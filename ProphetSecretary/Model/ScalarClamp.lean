import ProphetSecretary.Model.BoundarySlack
import ProphetSecretary.Model.EndpointProjectionConditional

/-!
# Uniform projection to an interior scalar interval

Paper correspondence: `lem:scalar-clamp`. The reward-boundary theorem and the
exact waiting endpoint gap supply both positive endpoint slacks. The explicit
projection width depends only on H and mu; the regret multiplier can be K=1.
All competing randomized policies remain unrestricted.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Model

lemma normalizedScalarGap_zero {n : ℕ} (P : Instance n) : normalizedScalarGap P 0=1-optimalCompetitiveRatio := by
  simp only [normalizedScalarGap,scalarGap,sub_zero,zero_mul,zero_add,
    optimalScalarValue_zero_rewardWeight P zero_le_one,mul_one]

lemma normalizedScalarGap_one {n : ℕ} (P : Instance n) :
    normalizedScalarGap P 1=optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum := by
  simp only [normalizedScalarGap,scalarGap,sub_self,one_mul,add_zero]

/-- Full uniform scalar clamp; the source constant K is one. The interval is
chosen before the size, law, policy, target and training-outcome regret. -/
theorem bounded_scalar_clamp (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu) :
    ∃ a : ℝ, a∈Ioo (0:ℝ) (1/2) ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) → mu≤P.expectedMaximum →
      ∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0:ℝ) 1 →
      π.normalizedRegret P (max a (min (1-a) lam))≤r →
      normalizedScalarGap P lam/2-r≤π.scalarObjective P lam (1-lam)-
        optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  obtain ⟨d,hd,hSlack⟩ := bounded_reward_boundary_slack H mu hmu
  let d0 := min d (1-optimalCompetitiveRatio)
  have hd0 : 0<d0 := lt_min hd (by linarith only [optimalCompetitiveRatio_le_threeQuarters])
  let a := endpointProjectionWidth (H:ℝ) d0
  have ha := endpointProjectionWidth_properties H.property hd0
  refine ⟨a,ha.1,?_⟩
  intro n P hcap hMean π lam r hlam hRegret
  have hLeft : d0≤normalizedScalarGap P 0 := by
    rw [normalizedScalarGap_zero]
    exact min_le_right _ _
  have hRight : d0≤normalizedScalarGap P 1 := by
    rw [normalizedScalarGap_one]
    exact (min_le_left _ _).trans (hSlack n P hcap hMean)
  exact π.scalar_clamp_of_endpoint_slack P H.property hd0 hcap hLeft hRight hlam hRegret

end ProphetSecretary.Model
