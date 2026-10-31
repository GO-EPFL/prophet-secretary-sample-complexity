import ProphetSecretary.Probability.WideLikelihoodPath

/-!
# Fisher information throughout the wider likelihood neighborhood

Current scores have absolute value at most two and information at most twice
the base information. These constants hold on the entire half interval.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

lemma likelihoodWideTilt_score_memLp_two (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1)
    (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 2) (i : Fin n) :
    MemLp (tiltedScore (h i) θ) 2 ((P.likelihoodWideTilt h hh hb hm θ hθ).law i) := by
  apply MemLp.of_bound (measurable_tiltedScore (hh i) θ).aestronglyMeasurable 2
  apply (tiltLaw_absolutelyContinuous (P.law i) (h i) θ).ae_le
  exact (hb i).mono (fun a ha ↦ by
    simpa only [Real.norm_eq_abs, tiltedScore, tiltFactor] using tiltedScore_half_abs_le hθ ha)

lemma information_likelihoodWideTilt_tiltedScore_le (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1)
    (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    information (P.likelihoodWideTilt h hh hb hm θ hθ).law (fun i ↦ tiltedScore (h i) θ) ≤
      2 * information P.law h := by
  unfold information
  calc
    _ ≤ ∑ i : Fin n, 2 * ∫ a, h i a ^ 2 ∂P.law i := Finset.sum_le_sum
      (fun i _ ↦ tiltedScore_half_secondMoment_le (hh i) (hb i) hθ)
    _ = _ := (Finset.mul_sum _ _ _).symm

end ProphetSecretary.Model.Instance
