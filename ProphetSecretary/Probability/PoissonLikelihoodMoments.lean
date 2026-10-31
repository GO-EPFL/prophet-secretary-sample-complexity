import ProphetSecretary.Probability.PoissonLikelihoodCalculus
import ProphetSecretary.Probability.PoissonRateDensity
import ProphetSecretary.Probability.PoissonCenteredScore

/-!
# Exact tilted moments and the Poisson likelihood Hessian bound

A positive multiplier changes the actual Poisson rate. Its centered second
moment gives the L¹ bound 2rate/(1+θ) for the second likelihood derivative,
without a deterministic count cutoff.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace ProphetSecretary.Probability
open ProphetSecretary.Limiting

lemma poissonLikelihood_eq_scale (rate a : ℝ≥0) (θ : ℝ) (ha : (a : ℝ)=1+θ) (n : ℕ) :
    poissonLikelihood rate θ n=poissonScaleLikelihood rate a n := by
  unfold poissonLikelihood poissonScaleLikelihood
  rw [ha]
  have hExponent : -(rate : ℝ)*θ=(1-(1+θ))*(rate : ℝ) := by ring
  rw [hExponent]

private lemma normalized_score_eq (rate a : ℝ≥0) (ha : 0 < a) (n : ℕ) :
    (n : ℝ)/(a : ℝ)-(rate : ℝ)=poissonCenteredScore (rate*a) n/(a : ℝ) := by
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha
  unfold poissonCenteredScore
  rw [NNReal.coe_mul]
  apply (eq_div_iff ha').mpr
  calc
    _ = ((n : ℝ)/(a : ℝ))*(a : ℝ)-(rate : ℝ)*(a : ℝ) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ ha']

private lemma normalized_score_sq_integrable (rate a : ℝ≥0) (ha : 0 < a) :
    Integrable (fun n : ℕ => ((n : ℝ)/(a : ℝ)-(rate : ℝ))^2) (poissonMeasure (rate*a)) := by
  have h := (integrable_poissonCenteredScore_sq (rate*a)).div_const ((a : ℝ)^2)
  apply h.congr
  exact Eventually.of_forall (fun n => by
    change (poissonCenteredScore (rate*a) n)^2/(a : ℝ)^2=((n : ℝ)/(a : ℝ)-(rate : ℝ))^2
    rw [normalized_score_eq rate a ha n,div_pow])

private lemma integral_normalized_score_sq (rate a : ℝ≥0) (ha : 0 < a) :
    (∫ n : ℕ, ((n : ℝ)/(a : ℝ)-(rate : ℝ))^2 ∂poissonMeasure (rate*a))=(rate : ℝ)/(a : ℝ) := by
  have hFunction : (fun n : ℕ => ((n : ℝ)/(a : ℝ)-(rate : ℝ))^2)=
      fun n => (poissonCenteredScore (rate*a) n)^2/(a : ℝ)^2 := by
    funext n
    rw [normalized_score_eq rate a ha n,div_pow]
  rw [hFunction,integral_div,integral_poissonCenteredScore_sq,NNReal.coe_mul,pow_two,
    mul_div_mul_right _ _ (show (a : ℝ) ≠ 0 from ne_of_gt ha)]

private lemma integral_scaled_count_div_sq (rate a : ℝ≥0) (ha : 0 < a) :
    (∫ n : ℕ, (n : ℝ)/(a : ℝ)^2 ∂poissonMeasure (rate*a))=(rate : ℝ)/(a : ℝ) := by
  rw [integral_div,integral_poisson_first,NNReal.coe_mul,pow_two,
    mul_div_mul_right _ _ (show (a : ℝ) ≠ 0 from ne_of_gt ha)]

lemma poissonLikelihoodSecond_integrable_and_bound (rate : ℝ≥0) {θ : ℝ} (hθ : 0 < 1+θ) :
    Integrable (poissonLikelihoodSecond rate θ) (poissonMeasure rate) ∧
      (∫ n, |poissonLikelihoodSecond rate θ n| ∂poissonMeasure rate) ≤ 2*(rate : ℝ)/(1+θ) := by
  let a : ℝ≥0 := ⟨1+θ,hθ.le⟩
  have ha : 0 < a := hθ
  let F := fun n : ℕ => ((n : ℝ)/(1+θ)-(rate : ℝ))^2+(n : ℝ)/(1+θ)^2
  have hScoreI : Integrable (fun n : ℕ => ((n : ℝ)/(1+θ)-(rate : ℝ))^2) (poissonMeasure (rate*a)) :=
    normalized_score_sq_integrable rate a ha
  have hCountI : Integrable (fun n : ℕ => (n : ℝ)/(1+θ)^2) (poissonMeasure (rate*a)) :=
    (poisson_first_integrable (rate*a)).div_const _
  have hFI : Integrable F (poissonMeasure (rate*a)) := hScoreI.add hCountI
  have hProduct := integrable_poisson_scale_product rate a hFI
  have hRhsI : Integrable (fun n => poissonLikelihood rate θ n*F n) (poissonMeasure rate) := by
    apply hProduct.congr
    exact Eventually.of_forall (fun n => congrArg (fun t => t*F n)
      (poissonLikelihood_eq_scale rate a θ rfl n).symm)
  have hPoint (n : ℕ) : |poissonLikelihoodSecond rate θ n| ≤ poissonLikelihood rate θ n*F n := by
    have hL0 : 0 ≤ poissonLikelihood rate θ n :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg hθ.le n)
    rw [poissonLikelihoodSecond,abs_mul,abs_of_nonneg hL0]
    apply mul_le_mul_of_nonneg_left _ hL0
    calc
      _ ≤ |((n : ℝ)/(1+θ)-(rate : ℝ))^2|+|(n : ℝ)/(1+θ)^2| := abs_sub _ _
      _ = F n := by
        rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (sq_nonneg _))]
  have hSecondI : Integrable (poissonLikelihoodSecond rate θ) (poissonMeasure rate) :=
    hRhsI.mono' (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall (fun n => by simpa only [Real.norm_eq_abs] using hPoint n))
  have hMean : (∫ n, poissonLikelihood rate θ n*F n ∂poissonMeasure rate)=
      ∫ n, F n ∂poissonMeasure (rate*a) := by
    rw [integral_poisson_scale]
    apply integral_congr_ae
    exact Eventually.of_forall (fun n => congrArg (fun t => t*F n) (poissonLikelihood_eq_scale rate a θ rfl n))
  have hRhs : (∫ n, F n ∂poissonMeasure (rate*a))=2*(rate : ℝ)/(1+θ) := by
    change (∫ n, ((n : ℝ)/(a : ℝ)-(rate : ℝ))^2+(n : ℝ)/(a : ℝ)^2 ∂poissonMeasure (rate*a))=_
    rw [integral_add (f := fun n : ℕ => ((n : ℝ)/(a : ℝ)-(rate : ℝ))^2)
      (g := fun n : ℕ => (n : ℝ)/(a : ℝ)^2) hScoreI hCountI,
      integral_normalized_score_sq rate a ha,integral_scaled_count_div_sq rate a ha]
    change (rate : ℝ)/(1+θ)+(rate : ℝ)/(1+θ)=_
    ring
  exact ⟨hSecondI,(integral_mono_ae hSecondI.abs hRhsI (Eventually.of_forall hPoint)).trans_eq (hMean.trans hRhs)⟩

lemma poissonLikelihoodSecond_L1_uniform (rate : ℝ≥0) {θ : ℝ} (hθ : |θ| ≤ 1/2) :
    (∫ n, |poissonLikelihoodSecond rate θ n| ∂poissonMeasure rate) ≤ 4*(rate : ℝ) := by
  have hLower : 1/2 ≤ 1+θ := by linarith only [(abs_le.mp hθ).1]
  have hPositive : 0 < 1+θ := (by norm_num : (0 : ℝ) < 1/2).trans_le hLower
  apply (poissonLikelihoodSecond_integrable_and_bound rate hPositive).2.trans
  apply (div_le_iff₀ hPositive).mpr
  have h := mul_le_mul_of_nonneg_left hLower (show 0 ≤ 4*(rate : ℝ) by positivity)
  nlinarith only [h]

end ProphetSecretary.Probability
