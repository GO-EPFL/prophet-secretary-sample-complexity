import ProphetSecretary.Probability.PoissonRateDensity

/-!
# Geometrically weighted Poisson moments

The exact change-of-rate density gives the exponential moment and its first
two weighted moments, with explicit constants for every nonnegative rate and
geometric weight. These bounds provide domination for likelihood calculus.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProphetSecretary.Probability
open ProphetSecretary.Limiting

lemma integrable_poisson_geometric_zero (rate a : ℝ≥0) :
    Integrable (fun n : ℕ => (a : ℝ)^n) (poissonMeasure rate) := by
  simpa only [mul_one] using integrable_poisson_geometric rate a
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℕ => (1 : ℝ)) (poissonMeasure (rate*a)))

lemma integral_poisson_geometric_zero (rate a : ℝ≥0) :
    (∫ n : ℕ, (a : ℝ)^n ∂poissonMeasure rate)=Real.exp ((rate : ℝ)*((a : ℝ)-1)) := by
  simpa only [mul_one,integral_const,probReal_univ,one_smul] using
    integral_poisson_geometric rate a (fun _ => (1 : ℝ))

lemma integrable_poisson_geometric_first (rate a : ℝ≥0) :
    Integrable (fun n : ℕ => (a : ℝ)^n*(n : ℝ)) (poissonMeasure rate) :=
  integrable_poisson_geometric rate a (poisson_first_integrable (rate*a))

lemma integral_poisson_geometric_first (rate a : ℝ≥0) :
    (∫ n : ℕ, (a : ℝ)^n*(n : ℝ) ∂poissonMeasure rate)=
      Real.exp ((rate : ℝ)*((a : ℝ)-1))*((rate : ℝ)*(a : ℝ)) := by
  rw [integral_poisson_geometric,integral_poisson_first,NNReal.coe_mul]

lemma integrable_poisson_geometric_second (rate a : ℝ≥0) :
    Integrable (fun n : ℕ => (a : ℝ)^n*(n : ℝ)^2) (poissonMeasure rate) :=
  integrable_poisson_geometric rate a (poisson_second_integrable (rate*a))

lemma integral_poisson_geometric_second (rate a : ℝ≥0) :
    (∫ n : ℕ, (a : ℝ)^n*(n : ℝ)^2 ∂poissonMeasure rate)=
      Real.exp ((rate : ℝ)*((a : ℝ)-1))*(((rate : ℝ)*(a : ℝ))^2+(rate : ℝ)*(a : ℝ)) := by
  rw [integral_poisson_geometric,integral_poisson_second,NNReal.coe_mul]

end ProphetSecretary.Probability
