import ProphetSecretary.Probability.BandScore
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Complex.Exponential

/-!
# Uniform moments of nonidentical independent band counts

The complete-vector count in a measurable band has exponential moment at most
exp((exp(t)−1)Λ), where Λ is the sum of its marginal probabilities. This yields
explicit moments and uniform truncation bounds of every fixed natural order,
independently of the finite instance size. Counts remain analytical variables;
no policy learns future occurrences from them.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {n : ℕ}

lemma measurable_countIn {B : Set ℝ} (hB : MeasurableSet B) : Measurable (@countIn n B) :=
  Finset.measurable_sum _ (fun i _ => (measurable_const.indicator hB).comp (measurable_pi_apply i))

lemma countIn_bounds (B : Set ℝ) (x : Fin n → ℝ) : 0 ≤ countIn B x ∧ countIn B x ≤ n := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    by_cases hi : x i ∈ B <;> simp [hi]
  · have h : (∑ i, B.indicator (fun _ => (1 : ℝ)) (x i)) ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x i ∈ B <;> simp [hi]
    simpa only [countIn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using h

variable (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

noncomputable def bandIntensity (B : Set ℝ) : ℝ := ∑ i, (μ i).real B
omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma bandIntensity_nonnegative (B : Set ℝ) : 0 ≤ bandIntensity μ B :=
  Finset.sum_nonneg fun _ _ => measureReal_nonneg

lemma integrable_countIn_pow {B : Set ℝ} (hB : MeasurableSet B) (r : ℕ) :
    Integrable (fun x : Fin n → ℝ => countIn B x ^ r) (Measure.pi μ) := by
  exact integrable_pow_of_bound (measurable_countIn hB) (Nat.cast_nonneg n)
    (Eventually.of_forall fun x => by rw [abs_of_nonneg (countIn_bounds B x).1]; exact (countIn_bounds B x).2) r

lemma integrable_exp_countIn {B : Set ℝ} (hB : MeasurableSet B) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Fin n → ℝ => Real.exp (t * countIn B x)) (Measure.pi μ) := by
  apply Integrable.of_bound ((measurable_const.mul (measurable_countIn hB)).exp).aestronglyMeasurable (Real.exp (t * n))
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (countIn_bounds B x).2 ht)

lemma exp_indicator_eq (B : Set ℝ) (x t : ℝ) :
    Real.exp (t * B.indicator (fun _ => (1 : ℝ)) x) =
      1 + (Real.exp t - 1) * B.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ B <;> simp [hx]

/-- Exact product moment for arbitrary nonidentical marginal laws. -/
theorem integral_exp_countIn {B : Set ℝ} (hB : MeasurableSet B) (t : ℝ) :
    (∫ x : Fin n → ℝ, Real.exp (t * countIn B x) ∂Measure.pi μ) =
      ∏ i, (1 + (μ i).real B * (Real.exp t - 1)) := by
  have heq : (fun x : Fin n → ℝ => Real.exp (t * countIn B x)) =
      fun x => ∏ i, Real.exp (t * B.indicator (fun _ => (1 : ℝ)) (x i)) := by
    funext x
    unfold countIn
    rw [Finset.mul_sum,Real.exp_sum]
  rw [heq,integral_fintype_prod_eq_prod (μ := μ) (fun (_ : Fin n) (x : ℝ) => Real.exp (t * B.indicator (fun _ => (1 : ℝ)) x))]
  apply Finset.prod_congr rfl
  intro i _
  simp_rw [exp_indicator_eq]
  rw [integral_add (integrable_const 1) (((integrable_const (1 : ℝ)).indicator hB).const_mul (Real.exp t - 1)),
    integral_const,integral_const_mul,integral_indicator_const 1 hB]
  simp only [probReal_univ,smul_eq_mul,mul_one]
  ring

/-- Exponential moment bound depending on Λ, not on n. -/
theorem integral_exp_countIn_le {B : Set ℝ} (hB : MeasurableSet B) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : Fin n → ℝ, Real.exp (t * countIn B x) ∂Measure.pi μ) ≤
      Real.exp ((Real.exp t - 1) * bandIntensity μ B) := by
  rw [integral_exp_countIn μ hB t]
  have hz : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  calc
    _ ≤ ∏ i, Real.exp ((μ i).real B * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg zero_le_one (mul_nonneg measureReal_nonneg hz)
      · intro i _
        have h := Real.add_one_le_exp ((μ i).real B * (Real.exp t - 1))
        linarith only [h]
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      unfold bandIntensity
      rw [← Finset.sum_mul,mul_comm]

/-- Explicit raw moments from the nonnegative exponential series. -/
theorem integral_countIn_pow_le {B : Set ℝ} (hB : MeasurableSet B) (r : ℕ) :
    (∫ x : Fin n → ℝ, countIn B x ^ r ∂Measure.pi μ) ≤
      (r.factorial : ℝ) * Real.exp ((Real.exp 1 - 1) * bandIntensity μ B) := by
  have hfac : 0 < (r.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have hpt (x : Fin n → ℝ) : countIn B x ^ r ≤ (r.factorial : ℝ) * Real.exp (countIn B x) := by
    have h := Real.pow_div_factorial_le_exp (countIn B x) (countIn_bounds B x).1 r
    have hm := (div_le_iff₀ hfac).mp h
    nlinarith only [hm]
  have hE : Integrable (fun x : Fin n → ℝ => Real.exp (countIn B x)) (Measure.pi μ) := by
    simpa only [one_mul] using integrable_exp_countIn μ hB (t := 1) zero_le_one
  have hi := integral_mono (integrable_countIn_pow μ hB r) (hE.const_mul (r.factorial : ℝ)) hpt
  rw [integral_const_mul] at hi
  have hexp := integral_exp_countIn_le μ hB (t := 1) zero_le_one
  simp only [one_mul] at hexp
  exact hi.trans (mul_le_mul_of_nonneg_left hexp hfac.le)

/-- Uniform raw moments for any family with a common intensity bound. -/
theorem integral_countIn_pow_le_of_intensity {B : Set ℝ} (hB : MeasurableSet B)
    {Λ : ℝ} (hΛ : bandIntensity μ B ≤ Λ) (r : ℕ) :
    (∫ x : Fin n → ℝ, countIn B x ^ r ∂Measure.pi μ) ≤
      (r.factorial : ℝ) * Real.exp ((Real.exp 1 - 1) * Λ) := by
  apply (integral_countIn_pow_le μ hB r).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hΛ (sub_nonneg.mpr (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr zero_le_one))

/-- Moment truncation error of order r is O(1/R), uniformly when Λ is bounded.
The power r+1 is controlled by the preceding explicit exponential estimate. -/
theorem integral_countIn_pow_tail_le {B : Set ℝ} (hB : MeasurableSet B)
    {Λ R : ℝ} (hΛ : bandIntensity μ B ≤ Λ) (hR : 0 < R) (r : ℕ) :
    (∫ x : Fin n → ℝ, {x | R < countIn B x}.indicator (fun x => countIn B x ^ r) x ∂Measure.pi μ) ≤
      ((r+1).factorial : ℝ) * Real.exp ((Real.exp 1 - 1) * Λ) / R := by
  have hset : MeasurableSet {x : Fin n → ℝ | R < countIn B x} :=
    measurableSet_lt measurable_const (measurable_countIn hB)
  have hpoint (x : Fin n → ℝ) : {x | R < countIn B x}.indicator (fun x => countIn B x ^ r) x ≤ countIn B x ^ (r+1) / R := by
    by_cases hx : R < countIn B x
    · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_pos hx]
      apply (le_div_iff₀ hR).mpr
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left hx.le (pow_nonneg (countIn_bounds B x).1 r)
    · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg hx]
      exact div_nonneg (pow_nonneg (countIn_bounds B x).1 (r+1)) hR.le
  have hi := integral_mono ((integrable_countIn_pow μ hB r).indicator hset)
    ((integrable_countIn_pow μ hB (r+1)).div_const R) hpoint
  rw [integral_div] at hi
  exact hi.trans (div_le_div_of_nonneg_right (integral_countIn_pow_le_of_intensity μ hB hΛ (r+1)) hR.le)

end ProphetSecretary.Probability
