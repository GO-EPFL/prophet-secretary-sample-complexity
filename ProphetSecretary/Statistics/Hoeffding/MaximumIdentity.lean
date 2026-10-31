import ProphetSecretary.Statistics.Hoeffding.Decomposition
import ProphetSecretary.Statistics.EmpiricalMaximumVariance

/-!
# The exact empirical expected-maximum variance formula

Paper correspondence: `eq:bayes-maximum-variance`. The component variances are
those of the original complete maximum. Its bounded representative agrees
almost surely, and actual conditional averaging preserves that equality, so
no clipping-induced change of the Hoeffding variances is assumed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability.Hoeffding
open ProphetSecretary.Statistics.Hoeffding
variable {n k : ℕ} [NeZero k]

/-- Exact Hoeffding identity for the actual empirical expected maximum. -/
theorem Instance.empiricalMaximum_hoeffding_variance_identity (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k) =
      ∑ A ∈ nonemptySubsets (Fin n), ((k : ℝ)^A.card)⁻¹ * variance (component P.law A Instance.maximum) P.valuesLaw := by
  have hhat := variance_congr (P.empiricalExpectedMaximum_eq_productAverage_ae (k := k) H hcap)
  have hvar := variance_empiricalMean (k := k) P.law (measurable_boundedMaximum H) H (boundedMaximum_abs_le H)
  change variance (empiricalMean (k := k) (boundedMaximum H))
      (Measure.pi (fun q : Fin n × Fin k => P.law q.1)) = _ at hvar
  calc
    _ = variance (empiricalMean (k := k) (boundedMaximum H)) (P.trainingCoordinateLaw k) := hhat
    _ = ∑ A ∈ nonemptySubsets (Fin n), ((k : ℝ)^A.card)⁻¹ * variance (component P.law A (boundedMaximum H)) P.valuesLaw := hvar
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      exact congrArg (fun v : ℝ => ((k : ℝ)^A.card)⁻¹*v)
        (variance_congr (component_congr_ae P.law A (P.boundedMaximum_eq_maximum_ae H hcap)))

/-- All displayed clauses of `eq:bayes-maximum-variance`, uniformly in finite
instance size and including zero expected maxima. -/
theorem Instance.empiricalMaximum_variance_formula_and_bounds (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) :
    variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k) =
      (∑ A ∈ nonemptySubsets (Fin n), ((k : ℝ)^A.card)⁻¹ * variance (component P.law A Instance.maximum) P.valuesLaw) ∧
    variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k) ≤ variance Instance.maximum P.valuesLaw/(k : ℝ) ∧
    variance Instance.maximum P.valuesLaw/(k : ℝ) ≤ P.expectedMaximum/(k : ℝ) :=
  ⟨P.empiricalMaximum_hoeffding_variance_identity 1 hcap,P.variance_empiricalExpectedMaximum_le 1 hcap,
    div_le_div_of_nonneg_right (P.variance_maximum_le_expectedMaximum hcap) (Nat.cast_nonneg k)⟩

end ProphetSecretary.Model
