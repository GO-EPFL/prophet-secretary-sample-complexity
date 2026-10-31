import ProphetSecretary.Limiting.PoissonCountMoments
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The centered Poisson count score

The mean, square integrability and exact variance are proved from the actual
first and second Poisson moments, including rate zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace ProphetSecretary.Probability
open ProphetSecretary.Limiting

noncomputable def poissonCenteredScore (rate : ℝ≥0) (n : ℕ) : ℝ := (n : ℝ)-(rate : ℝ)

lemma measurable_poissonCenteredScore (rate : ℝ≥0) : Measurable (poissonCenteredScore rate) :=
  measurable_of_countable _

lemma integrable_poissonCenteredScore (rate : ℝ≥0) :
    Integrable (poissonCenteredScore rate) (poissonMeasure rate) :=
  (poisson_first_integrable rate).sub (integrable_const _)

lemma integral_poissonCenteredScore (rate : ℝ≥0) :
    (∫ n, poissonCenteredScore rate n ∂poissonMeasure rate)=0 := by
  change (∫ n : ℕ, (n : ℝ)-(rate : ℝ) ∂poissonMeasure rate)=0
  rw [integral_sub (poisson_first_integrable rate) (integrable_const _),integral_poisson_first,integral_const]
  simp only [probReal_univ,one_smul,sub_self]

lemma integrable_poissonCenteredScore_sq (rate : ℝ≥0) :
    Integrable (fun n => (poissonCenteredScore rate n)^2) (poissonMeasure rate) := by
  have hPoly := ((poisson_second_integrable rate).sub
    ((poisson_first_integrable rate).const_mul (2*(rate : ℝ)))).add (integrable_const ((rate : ℝ)^2))
  apply hPoly.congr
  exact Eventually.of_forall (fun n => by change (n : ℝ)^2-2*(rate : ℝ)*(n : ℝ)+(rate : ℝ)^2=((n : ℝ)-(rate : ℝ))^2; ring)

lemma integral_poissonCenteredScore_sq (rate : ℝ≥0) :
    (∫ n, (poissonCenteredScore rate n)^2 ∂poissonMeasure rate)=(rate : ℝ) := by
  have hFunction : (fun n => (poissonCenteredScore rate n)^2)=
      fun n : ℕ => (n : ℝ)^2-2*(rate : ℝ)*(n : ℝ)+(rate : ℝ)^2 := by
    funext n
    unfold poissonCenteredScore
    ring
  rw [hFunction,
    integral_add (f := fun n : ℕ => (n : ℝ)^2-2*(rate : ℝ)*(n : ℝ))
      (g := fun _ : ℕ => (rate : ℝ)^2) ((poisson_second_integrable rate).sub
        ((poisson_first_integrable rate).const_mul (2*(rate : ℝ)))) (integrable_const _),
    integral_sub (f := fun n : ℕ => (n : ℝ)^2) (g := fun n : ℕ => 2*(rate : ℝ)*(n : ℝ))
      (poisson_second_integrable rate) ((poisson_first_integrable rate).const_mul (2*(rate : ℝ))),
    integral_const_mul,integral_poisson_second,integral_poisson_first,integral_const]
  simp only [probReal_univ,one_smul]
  ring

lemma poissonCenteredScore_memLp_two (rate : ℝ≥0) :
    MemLp (poissonCenteredScore rate) 2 (poissonMeasure rate) :=
  (memLp_two_iff_integrable_sq (measurable_poissonCenteredScore rate).aestronglyMeasurable).mpr
    (integrable_poissonCenteredScore_sq rate)

end ProphetSecretary.Probability
