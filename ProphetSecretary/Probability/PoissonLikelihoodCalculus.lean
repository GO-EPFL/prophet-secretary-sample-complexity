import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Pointwise Poisson likelihood derivatives

The count n is fixed while the parameter varies. The formulas hold on the
positive-rate-multiplier domain 1+θ>0, including n=0 and rate zero.
-/

open MeasureTheory
open scoped NNReal

namespace ProphetSecretary.Probability

noncomputable def poissonLikelihood (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(rate : ℝ)*θ)*(1+θ)^n

noncomputable def poissonLikelihoodFirst (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : ℝ :=
  poissonLikelihood rate θ n*((n : ℝ)/(1+θ)-(rate : ℝ))

noncomputable def poissonLikelihoodSecond (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : ℝ :=
  poissonLikelihood rate θ n*(((n : ℝ)/(1+θ)-(rate : ℝ))^2-(n : ℝ)/(1+θ)^2)

@[simp] lemma poissonLikelihood_zero (rate : ℝ≥0) (n : ℕ) : poissonLikelihood rate 0 n=1 := by
  simp [poissonLikelihood]

@[simp] lemma poissonLikelihoodFirst_zero (rate : ℝ≥0) (n : ℕ) :
    poissonLikelihoodFirst rate 0 n=(n : ℝ)-(rate : ℝ) := by simp [poissonLikelihoodFirst]

private lemma nat_mul_pow_pred (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (n : ℝ)*x^(n-1)=x^n*(n : ℝ)/x := by
  cases n with
  | zero => simp
  | succ n =>
    apply (eq_div_iff hx).mpr
    simp only [Nat.succ_sub_one,pow_succ]
    ring

lemma hasDerivAt_poissonLikelihood (rate : ℝ≥0) (θ : ℝ) (n : ℕ) (hθ : 0 < 1+θ) :
    HasDerivAt (fun u => poissonLikelihood rate u n) (poissonLikelihoodFirst rate θ n) θ := by
  have hExp : HasDerivAt (fun u : ℝ => Real.exp (-(rate : ℝ)*u))
      (Real.exp (-(rate : ℝ)*θ)*(-(rate : ℝ))) θ := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id θ).const_mul (-(rate : ℝ))).exp
  have hPower : HasDerivAt (fun u : ℝ => (1+u)^n) ((n : ℝ)*(1+θ)^(n-1)) θ := by
    have hRaw := ((hasDerivAt_id θ).const_add 1).pow n
    change HasDerivAt (fun u : ℝ => (1+u)^n) ((n : ℝ)*(1+θ)^(n-1)*1) θ at hRaw
    simpa only [mul_one] using hRaw
  have h := hExp.mul hPower
  have hCoefficient :
      (Real.exp (-(rate : ℝ)*θ)*(-(rate : ℝ)))*(1+θ)^n+
        Real.exp (-(rate : ℝ)*θ)*((n : ℝ)*(1+θ)^(n-1))=poissonLikelihoodFirst rate θ n := by
    rw [nat_mul_pow_pred (1+θ) hθ.ne' n]
    unfold poissonLikelihoodFirst poissonLikelihood
    ring
  rw [hCoefficient] at h
  exact h

lemma hasDerivAt_poissonLikelihoodFirst (rate : ℝ≥0) (θ : ℝ) (n : ℕ) (hθ : 0 < 1+θ) :
    HasDerivAt (fun u => poissonLikelihoodFirst rate u n) (poissonLikelihoodSecond rate θ n) θ := by
  have hRatio := (hasDerivAt_const θ (n : ℝ)).div ((hasDerivAt_id θ).const_add 1) hθ.ne'
  have hScore : HasDerivAt (fun u : ℝ => (n : ℝ)/(1+u)-(rate : ℝ))
      (-(n : ℝ)/(1+θ)^2) θ := by
    have hRaw := hRatio.sub_const (rate : ℝ)
    change HasDerivAt (fun u : ℝ => (n : ℝ)/(1+u)-(rate : ℝ))
      ((0*(1+θ)-(n : ℝ)*1)/(1+θ)^2) θ at hRaw
    simpa only [zero_mul,mul_one,zero_sub] using hRaw
  have h := (hasDerivAt_poissonLikelihood rate θ n hθ).mul hScore
  have hCoefficient : poissonLikelihoodFirst rate θ n*((n : ℝ)/(1+θ)-(rate : ℝ))+
      poissonLikelihood rate θ n*(-(n : ℝ)/(1+θ)^2)=poissonLikelihoodSecond rate θ n := by
    unfold poissonLikelihoodFirst poissonLikelihoodSecond
    ring
  rw [hCoefficient] at h
  exact h

lemma measurable_poissonLikelihood_joint (rate : ℝ≥0) :
    Measurable (fun z : ℝ × ℕ => poissonLikelihood rate z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro n
  unfold poissonLikelihood
  fun_prop

lemma measurable_poissonLikelihoodFirst_joint (rate : ℝ≥0) :
    Measurable (fun z : ℝ × ℕ => poissonLikelihoodFirst rate z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro n
  unfold poissonLikelihoodFirst poissonLikelihood
  fun_prop

lemma measurable_poissonLikelihoodSecond_joint (rate : ℝ≥0) :
    Measurable (fun z : ℝ × ℕ => poissonLikelihoodSecond rate z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro n
  unfold poissonLikelihoodSecond poissonLikelihood
  fun_prop

end ProphetSecretary.Probability
