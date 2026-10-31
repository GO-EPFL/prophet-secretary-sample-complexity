import ProphetSecretary.Limiting.PoissonCountMoments
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Exact density for a change of Poisson rate

The scalar count law and all its weighted integrals are derived from actual
singleton probabilities. No moment or likelihood assertion is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Probability
open ProphetSecretary.Limiting

noncomputable def poissonScaleLikelihood (rate a : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp ((1-(a : ℝ))*(rate : ℝ))*(a : ℝ)^n

lemma poissonScaleLikelihood_nonnegative (rate a : ℝ≥0) (n : ℕ) :
    0 ≤ poissonScaleLikelihood rate a n := by unfold poissonScaleLikelihood; positivity

lemma poissonWeight_scaled (rate a : ℝ≥0) (n : ℕ) :
    poissonWeight (rate*a) n=poissonScaleLikelihood rate a n*poissonWeight rate n := by
  have hExp : Real.exp ((1-(a : ℝ))*(rate : ℝ))*Real.exp (-(rate : ℝ))=
      Real.exp (-((rate : ℝ)*(a : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold poissonWeight poissonScaleLikelihood
  rw [NNReal.coe_mul,mul_pow]
  calc
    _ = (Real.exp ((1-(a : ℝ))*(rate : ℝ))*Real.exp (-(rate : ℝ)))*
        ((rate : ℝ)^n*(a : ℝ)^n)/(n.factorial : ℝ) := by rw [hExp]
    _ = _ := by ring

lemma poissonMeasure_scaled_withDensity (rate a : ℝ≥0) :
    poissonMeasure (rate*a)=(poissonMeasure rate).withDensity
      (fun n => ENNReal.ofReal (poissonScaleLikelihood rate a n)) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton,withDensity_apply _ (measurableSet_singleton n),
    lintegral_singleton,poissonMeasure_singleton]
  change ENNReal.ofReal (poissonWeight (rate*a) n)=
    ENNReal.ofReal (poissonScaleLikelihood rate a n)*ENNReal.ofReal (poissonWeight rate n)
  rw [poissonWeight_scaled]
  exact ENNReal.ofReal_mul (poissonScaleLikelihood_nonnegative rate a n)

lemma integral_poisson_scale (rate a : ℝ≥0) (f : ℕ → ℝ) :
    (∫ n, f n ∂poissonMeasure (rate*a))=
      ∫ n, poissonScaleLikelihood rate a n*f n ∂poissonMeasure rate := by
  have hf : Measurable (fun n => ENNReal.ofReal (poissonScaleLikelihood rate a n)) := measurable_of_countable _
  rw [poissonMeasure_scaled_withDensity,
    integral_withDensity_eq_integral_toReal_smul hf (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun n => by
    change (ENNReal.ofReal (poissonScaleLikelihood rate a n)).toReal • f n=poissonScaleLikelihood rate a n*f n
    rw [ENNReal.toReal_ofReal (poissonScaleLikelihood_nonnegative rate a n),smul_eq_mul])

lemma integrable_poisson_scale_product (rate a : ℝ≥0) {f : ℕ → ℝ}
    (hf : Integrable f (poissonMeasure (rate*a))) :
    Integrable (fun n => poissonScaleLikelihood rate a n*f n) (poissonMeasure rate) := by
  have hDensity : Measurable (fun n => ENNReal.ofReal (poissonScaleLikelihood rate a n)) := measurable_of_countable _
  rw [poissonMeasure_scaled_withDensity] at hf
  have h := (integrable_withDensity_iff_integrable_smul' hDensity
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hf
  simpa only [ENNReal.toReal_ofReal (poissonScaleLikelihood_nonnegative rate a _),smul_eq_mul] using h

lemma poisson_geometric_factor (rate a : ℝ≥0) (n : ℕ) :
    (a : ℝ)^n=Real.exp ((rate : ℝ)*((a : ℝ)-1))*poissonScaleLikelihood rate a n := by
  have hExp : Real.exp ((rate : ℝ)*((a : ℝ)-1))*Real.exp ((1-(a : ℝ))*(rate : ℝ))=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  unfold poissonScaleLikelihood
  rw [← mul_assoc,hExp,one_mul]

lemma integral_poisson_geometric (rate a : ℝ≥0) (f : ℕ → ℝ) :
    (∫ n, (a : ℝ)^n*f n ∂poissonMeasure rate)=
      Real.exp ((rate : ℝ)*((a : ℝ)-1))*(∫ n, f n ∂poissonMeasure (rate*a)) := by
  calc
    _ = ∫ n, Real.exp ((rate : ℝ)*((a : ℝ)-1))*(poissonScaleLikelihood rate a n*f n) ∂poissonMeasure rate :=
      integral_congr_ae (Eventually.of_forall (fun n => by rw [poisson_geometric_factor]; ring))
    _ = _ := by rw [integral_const_mul,integral_poisson_scale]

lemma integrable_poisson_geometric (rate a : ℝ≥0) {f : ℕ → ℝ}
    (hf : Integrable f (poissonMeasure (rate*a))) :
    Integrable (fun n => (a : ℝ)^n*f n) (poissonMeasure rate) := by
  have h := (integrable_poisson_scale_product rate a hf).const_mul (Real.exp ((rate : ℝ)*((a : ℝ)-1)))
  convert h using 1
  funext n
  rw [poisson_geometric_factor]
  ring

end ProphetSecretary.Probability
