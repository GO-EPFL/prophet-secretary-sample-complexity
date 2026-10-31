import ProphetSecretary.Stability.LawCurvature

/-!
# Explicit quarter-neighborhood Fisher and first-moment bounds

The actual likelihood laws have marginal density 1+θh. Their current scores
are h/(1+θh). The constants 4/3 and 5/4 are uniform in the finite instance size.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ}

lemma likelihoodWidePath_law_quarter (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1)
    (hm : ∀ i, (∫ x, h i x ∂P.law i)=0) {θ : ℝ} (hθ : |θ|≤1/4) (i : Fin n) :
    (P.likelihoodWidePath h hh hb hm θ).law i=tiltLaw (P.law i) (h i) θ := by
  rw [P.law_curvature_model_transfer h hh hb hm hθ]
  rfl

lemma information_likelihoodWidePath_quarter_le (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1)
    (hm : ∀ i, (∫ x, h i x ∂P.law i)=0) {θ : ℝ} (hθ : |θ|≤1/4) :
    information (P.likelihoodWidePath h hh hb hm θ).law (fun i => tiltedScore (h i) θ)≤
      (4/3)*information P.law h := by
  unfold information
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [P.likelihoodWidePath_law_quarter h hh hb hm hθ i]
  exact tiltedScore_secondMoment_le (hh i) (hb i) hθ

lemma totalFirstMoment_likelihoodWidePath_quarter_le (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1)
    (hm : ∀ i, (∫ x, h i x ∂P.law i)=0) {θ : ℝ} (hθ : |θ|≤1/4) :
    (P.likelihoodWidePath h hh hb hm θ).totalFirstMoment≤(5/4)*P.totalFirstMoment := by
  unfold totalFirstMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hFactor : ∀ᵐ x ∂P.law i, 0≤tiltFactor (h i) θ x :=
    (hb i).mono (fun x hx => (by norm_num : (0:ℝ)≤3/4).trans (tiltFactor_bounds hθ hx).1)
  rw [P.likelihoodWidePath_law_quarter h hh hb hm hθ i]
  rw [integral_tiltLaw (hh i) hFactor (fun x : ℝ => x),← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((P.integrable_maximum_iff.mp hP i).const_mul (5/4:ℝ)) ?_
  · filter_upwards [hFactor,P.nonnegative i] with x hf hx
    exact mul_nonneg hf hx
  · filter_upwards [hb i,P.nonnegative i] with x hb' hx
    exact mul_le_mul_of_nonneg_right (tiltFactor_bounds hθ hb').2 hx
end ProphetSecretary.Model.Instance
