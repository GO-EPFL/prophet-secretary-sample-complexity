import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# First two Poisson count moments

The installed Poisson distribution supplies its actual mass function and
normalization. Shifting that normalized series proves the first and second
factorial moments used by the marked finite-intensity construction.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Nat

namespace ProphetSecretary.Limiting

noncomputable def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)

lemma poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n + 1) * (n + 1 : ℝ) = (r : ℝ) * poissonWeight r n := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

lemma hasSum_poisson_first (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonWeight r n * (n : ℝ)) (r : ℝ) := by
  have hs : HasSum (fun n : ℕ => poissonWeight r (n + 1) * (n + 1 : ℝ)) (r : ℝ) := by
    convert! (hasSum_one_poissonMeasure r).mul_left (r : ℝ) using 1
    · funext n
      exact poissonWeight_succ r n
    · simp only [mul_one]
  have h := HasSum.zero_add (f := fun n : ℕ => poissonWeight r n * (n : ℝ))
    (by simpa only [Nat.cast_add, Nat.cast_one] using hs)
  simpa only [Nat.cast_zero, mul_zero, zero_add] using h

lemma poisson_first_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  convert! (hasSum_poisson_first r).summable using 1
  funext n
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), poissonWeight]

lemma integral_poisson_first (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) := by
  have hi := hasSum_integral_poissonMeasure (poisson_first_integrable r)
  simp only [smul_eq_mul] at hi
  exact hi.unique (hasSum_poisson_first r)

lemma poissonWeight_second_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n + 1) * ((n + 1 : ℝ) * ((n + 1 : ℝ) - 1)) =
      (r : ℝ) * (poissonWeight r n * (n : ℝ)) := by
  have h := poissonWeight_succ r n
  nlinarith

lemma hasSum_poisson_factorial_second (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonWeight r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) := by
  have hs : HasSum (fun n : ℕ => poissonWeight r (n + 1) * ((n + 1 : ℝ) * ((n + 1 : ℝ) - 1)))
      ((r : ℝ) ^ 2) := by
    convert! (hasSum_poisson_first r).mul_left (r : ℝ) using 1
    · funext n
      exact poissonWeight_second_succ r n
    · ring
  have h := HasSum.zero_add (f := fun n : ℕ => poissonWeight r n * ((n : ℝ) * ((n : ℝ) - 1)))
    (by simpa only [Nat.cast_add, Nat.cast_one] using hs)
  simpa only [Nat.cast_zero, zero_mul, mul_zero, zero_add] using h

lemma poisson_factorial_second_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  convert! (hasSum_poisson_factorial_second r).summable using 1
  funext n
  have hn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    cases n with
    | zero => norm_num
    | succ n =>
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      nlinarith
  simp only [Real.norm_eq_abs, abs_of_nonneg hn, poissonWeight]

lemma integral_poisson_factorial_second (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) * ((n : ℝ) - 1) ∂poissonMeasure r) = (r : ℝ) ^ 2 := by
  have hi := hasSum_integral_poissonMeasure (poisson_factorial_second_integrable r)
  simp only [smul_eq_mul] at hi
  exact hi.unique (hasSum_poisson_factorial_second r)

lemma poisson_second_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) := by
  have hi := (poisson_factorial_second_integrable r).add (poisson_first_integrable r)
  convert! hi using 1
  funext n
  change (n : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) + (n : ℝ)
  ring

lemma integral_poisson_second (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + (r : ℝ) := by
  have he : (fun n : ℕ => (n : ℝ) ^ 2) = (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) + (n : ℝ)) := by
    funext n
    ring
  rw [he, integral_add (poisson_factorial_second_integrable r) (poisson_first_integrable r),
    integral_poisson_factorial_second, integral_poisson_first]

lemma lintegral_poisson_first (r : ℝ≥0) :
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = (r : ℝ≥0∞) := by
  have h := ofReal_integral_eq_lintegral_ofReal (poisson_first_integrable r)
    (Filter.Eventually.of_forall fun n => (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  rw [integral_poisson_first] at h
  simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal] using h.symm

lemma poisson_weights_first_ennreal (r : ℝ≥0) :
    (∑' n : ℕ, ENNReal.ofReal (poissonWeight r n) * (n : ℝ≥0∞)) = (r : ℝ≥0∞) := by
  have h := lintegral_poisson_first r
  rw [poissonMeasure, lintegral_sum_measure] at h
  simpa only [poissonWeight, lintegral_smul_measure, smul_eq_mul, lintegral_dirac] using h

end ProphetSecretary.Limiting
