import ProphetSecretary.Probability.PoissonLikelihoodCalculus
import ProphetSecretary.Probability.PoissonGeometricMoments

/-!
# Uniform local domination for Poisson likelihood calculus

The displayed envelopes use geometrically weighted first and second moments,
whose integrability is already established. Their constants depend on the
Poisson rate, not on an instance size or a deterministic bound on the count.
-/

open MeasureTheory
open scoped NNReal

namespace ProphetSecretary.Probability

lemma poissonLikelihood_local_bounds (rate : ℝ≥0) (n : ℕ) {θ : ℝ} (hθ : |θ| ≤ 1/2) :
    |poissonLikelihood rate θ n| ≤ Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^n ∧
    |poissonLikelihoodFirst rate θ n| ≤
      Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^n*(2*(n : ℝ)+(rate : ℝ)) ∧
    |poissonLikelihoodSecond rate θ n| ≤
      Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^n*((2*(n : ℝ)+(rate : ℝ))^2+4*(n : ℝ)) := by
  have hRate : 0 ≤ (rate : ℝ) := rate.property
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hLower : 1/2 ≤ 1+θ := by linarith only [(abs_le.mp hθ).1]
  have hUpper : 1+θ ≤ 3/2 := by linarith only [(abs_le.mp hθ).2]
  have hPositive : 0 < 1+θ := (by norm_num : (0 : ℝ) < 1/2).trans_le hLower
  have hExponent : -(rate : ℝ)*θ ≤ (rate : ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_left (show -θ ≤ 1/2 by linarith only [(abs_le.mp hθ).1]) hRate
    nlinarith only [h]
  have hExp := Real.exp_le_exp.mpr hExponent
  have hPower := pow_le_pow_left₀ hPositive.le hUpper n
  have hExp0 : 0 ≤ Real.exp ((rate : ℝ)/2) := (Real.exp_pos _).le
  have hA0 : 0 ≤ (3/2 : ℝ)^n := by positivity
  have hL0 : 0 ≤ poissonLikelihood rate θ n :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hPositive.le n)
  have hL : |poissonLikelihood rate θ n| ≤ Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^n := by
    rw [abs_of_nonneg hL0]
    exact mul_le_mul hExp hPower (pow_nonneg hPositive.le n) hExp0
  have hInverse : 1/(1+θ) ≤ (2 : ℝ) := (div_le_iff₀ hPositive).mpr (by linarith only [hLower])
  have hInverse0 : 0 ≤ 1/(1+θ) := div_nonneg (by norm_num) hPositive.le
  have hQuotient0 : 0 ≤ (n : ℝ)/(1+θ) := div_nonneg hN hPositive.le
  have hQuotient : (n : ℝ)/(1+θ) ≤ 2*(n : ℝ) := by
    calc
      _ = (n : ℝ)*(1/(1+θ)) := by ring
      _ ≤ (n : ℝ)*2 := mul_le_mul_of_nonneg_left hInverse hN
      _ = _ := mul_comm _ _
  have hScore : |(n : ℝ)/(1+θ)-(rate : ℝ)| ≤ 2*(n : ℝ)+(rate : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith only [hQuotient0,hQuotient,hRate,hN]
  have hInverseSquare : (1/(1+θ))^2 ≤ (4 : ℝ) :=
    (pow_le_pow_left₀ hInverse0 hInverse 2).trans_eq (by norm_num)
  have hQuotientSquare : (n : ℝ)/(1+θ)^2 ≤ 4*(n : ℝ) := by
    calc
      _ = (n : ℝ)*(1/(1+θ))^2 := by rw [div_pow,one_pow]; ring
      _ ≤ (n : ℝ)*4 := mul_le_mul_of_nonneg_left hInverseSquare hN
      _ = _ := mul_comm _ _
  have hScoreSquare : ((n : ℝ)/(1+θ)-(rate : ℝ))^2 ≤ (2*(n : ℝ)+(rate : ℝ))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hScore 2
  have hCore : |((n : ℝ)/(1+θ)-(rate : ℝ))^2-(n : ℝ)/(1+θ)^2| ≤
      (2*(n : ℝ)+(rate : ℝ))^2+4*(n : ℝ) := by
    calc
      _ ≤ |((n : ℝ)/(1+θ)-(rate : ℝ))^2|+|(n : ℝ)/(1+θ)^2| := abs_sub _ _
      _ = ((n : ℝ)/(1+θ)-(rate : ℝ))^2+(n : ℝ)/(1+θ)^2 := by
        rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (div_nonneg hN (sq_nonneg _))]
      _ ≤ _ := add_le_add hScoreSquare hQuotientSquare
  refine ⟨hL,?_,?_⟩
  · rw [poissonLikelihoodFirst,abs_mul]
    exact mul_le_mul hL hScore (abs_nonneg _) (mul_nonneg hExp0 hA0)
  · rw [poissonLikelihoodSecond,abs_mul]
    exact mul_le_mul hL hCore (abs_nonneg _) (mul_nonneg hExp0 hA0)

lemma integrable_poisson_firstEnvelope (rate : ℝ≥0) :
    Integrable (fun n : ℕ => Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^n*(2*(n : ℝ)+(rate : ℝ)))
      (ProbabilityTheory.poissonMeasure rate) := by
  let a : ℝ≥0 := ⟨3/2,by norm_num⟩
  have h := (((integrable_poisson_geometric_first rate a).const_mul 2).add
    ((integrable_poisson_geometric_zero rate a).const_mul (rate : ℝ))).const_mul (Real.exp ((rate : ℝ)/2))
  apply h.congr
  exact Filter.Eventually.of_forall (fun n => by change Real.exp ((rate : ℝ)/2)*(2*((3/2 : ℝ)^n*(n : ℝ))+(rate : ℝ)*(3/2 : ℝ)^n)=_; ring)

lemma integrable_poisson_secondEnvelope (rate : ℝ≥0) :
    Integrable (fun n : ℕ => Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^n*((2*(n : ℝ)+(rate : ℝ))^2+4*(n : ℝ)))
      (ProbabilityTheory.poissonMeasure rate) := by
  let a : ℝ≥0 := ⟨3/2,by norm_num⟩
  have h := ((((integrable_poisson_geometric_second rate a).const_mul 4).add
    ((integrable_poisson_geometric_first rate a).const_mul (4*(rate : ℝ)+4))).add
      ((integrable_poisson_geometric_zero rate a).const_mul ((rate : ℝ)^2))).const_mul (Real.exp ((rate : ℝ)/2))
  apply h.congr
  exact Filter.Eventually.of_forall (fun n => by
    change Real.exp ((rate : ℝ)/2)*(4*((3/2 : ℝ)^n*(n : ℝ)^2)+(4*(rate : ℝ)+4)*((3/2 : ℝ)^n*(n : ℝ))+
      (rate : ℝ)^2*(3/2 : ℝ)^n)=_
    ring)

end ProphetSecretary.Probability
