import ProphetSecretary.Limiting.HybridContinuationError
import ProphetSecretary.Limiting.BernoulliContinuationClockForms
import ProphetSecretary.Limiting.BernoulliClockMeanError

/-!
# Integrating continuation error over the actual complete clock law

The proved clock permutation separates the independent virtual block. At a
retained or anonymous candidate, its physical clock is fixed before virtual
clock averaging. The one-point bound has no retained-dimension or duration
factor; summing candidates leaves the explicit original-plus-anonymous count.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

/-- One actual original or anonymous candidate, with uniform explicit error. -/
theorem FiniteIntensityHybridInstance.integral_bernoulliContinuationError_le
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (j : ℕ)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (k : Fin (n+N)) :
    let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
    (∫ u : Fin (n+q+N) → ℝ, B.finiteDesignContinuationError (B.bernoulliApproximation hμ j) w c u k
      ∂Model.Instance.clocksLaw (n+q+N)) ≤ B.bernoulliClockErrorBound w j := by
  dsimp only
  let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
  let Q := B.bernoulliApproximation hμ j
  have hQ : Integrable Model.Instance.maximum Q.valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals _ _ _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  let f := fun u : Fin (n+q+N) → ℝ => B.finiteDesignContinuationError Q w c u k
  have hF : Integrable f (Model.Instance.clocksLaw (n+q+N)) := B.integrable_finiteDesignContinuationError Q hQ hw hc k
  change (∫ u, f u ∂Model.Instance.clocksLaw (n+q+N)) ≤ _
  apply Model.integral_le_of_anonymousVirtual_inner (n := n) (N := N) (q := q) f hF (B.bernoulliClockErrorBound w j)
  dsimp only [f]
  induction k using Fin.addCases with
  | left i =>
    filter_upwards [Model.Instance.clocks_mem_unitInterval (n := n)] with u hu
    refine Eventually.of_forall fun v => ?_
    simp_rw [B.finiteDesignContinuationError_retained_clockForm Q hQ hw hc u v _ i (hu i)]
    exact B.bernoulliClockState_absoluteMean_le ha hμ j u (hu i) (some i) hw
      (mul_nonneg hc (remainingTime (u i)).property)
  | right l =>
    refine Eventually.of_forall fun u => ?_
    filter_upwards [Model.Instance.clocks_mem_unitInterval (n := N)] with v hv
    simp_rw [B.finiteDesignContinuationError_anonymous_clockForm Q hQ hw hc u v _ l (hv l)]
    exact B.bernoulliClockState_absoluteMean_le ha hμ j u (hv l) none hw
      (mul_nonneg hc (remainingTime (v l)).property)

/-- The full error sum keeps its occurrence-count factor explicit. The
Poisson count is subsequently integrated under its constructed law. -/
theorem FiniteIntensityHybridInstance.integral_sum_bernoulliContinuationError_le
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (j : ℕ)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
    (∫ u : Fin (n+q+N) → ℝ, ∑ k : Fin (n+N),
      B.finiteDesignContinuationError (B.bernoulliApproximation hμ j) w c u k
      ∂Model.Instance.clocksLaw (n+q+N)) ≤ ((n : ℝ)+(N : ℝ))*B.bernoulliClockErrorBound w j := by
  dsimp only
  let Q := B.bernoulliApproximation hμ j
  have hQ : Integrable Model.Instance.maximum Q.valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals _ _ _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  rw [integral_finsetSum Finset.univ (fun k _ => B.integrable_finiteDesignContinuationError Q hQ hw hc k)]
  calc
    _ ≤ ∑ _k : Fin (n+N), B.bernoulliClockErrorBound w j := Finset.sum_le_sum fun k _ =>
      B.integral_bernoulliContinuationError_le ha hμ j hw hc k
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]

end ProphetSecretary.Limiting
