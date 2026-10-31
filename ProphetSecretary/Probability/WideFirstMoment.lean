import ProphetSecretary.Probability.WideLikelihoodPath

/-! # First moments under the wider likelihood family
Marginal densities are bounded by `3/2` on the half neighborhood. Summing the
marginal inequalities preserves a constant independent of instance size.
-/
open MeasureTheory
open scoped BigOperators
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ}

lemma totalFirstMoment_likelihoodWidePath_le (P : Instance n)
    (hP : Integrable maximum P.valuesLaw)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    (P.likelihoodWidePath h hh hb hm θ).totalFirstMoment ≤ (3 / 2 : ℝ) * P.totalFirstMoment := by
  rw [P.likelihoodWidePath_of_mem h hh hb hm hθ]
  unfold totalFirstMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hFactor : ∀ᵐ a ∂P.law i, 0 ≤ tiltFactor (h i) θ a :=
    (hb i).mono (fun a ha ↦ (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (tiltFactor_half_bounds hθ ha).1)
  change (∫ a, a ∂tiltLaw (P.law i) (h i) θ) ≤ _
  rw [integral_tiltLaw (hh i) hFactor (fun a : ℝ ↦ a), ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((P.integrable_maximum_iff.mp hP i).const_mul (3 / 2 : ℝ)) ?_
  · filter_upwards [hFactor, P.nonnegative i] with a hf ha
    exact mul_nonneg hf ha
  · filter_upwards [hb i, P.nonnegative i] with a hb' ha
    exact mul_le_mul_of_nonneg_right (tiltFactor_half_bounds hθ hb').2 ha

end ProphetSecretary.Model.Instance
