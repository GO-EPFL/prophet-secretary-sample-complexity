import ProphetSecretary.Probability.LikelihoodWorldIntegration
import ProphetSecretary.Probability.WideLikelihoodPath

/-! # Rebasing the actual complete-world law
The density identity changes only the offer coordinates. It therefore applies
also to analytical losses that depend on clocks or on values after stopping.
-/
open MeasureTheory
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma integral_likelihoodWidePath_rebase (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {θ δ : ℝ} (hθ : |θ| ≤ 1 / 2) (hδ : |2 * δ| ≤ 1 / 4) (hNew : |θ + δ| ≤ 1 / 2)
    (F : World n Seed → ℝ) :
    (∫ ω, F ω ∂(P.likelihoodWidePath h hh hb hm (θ + δ)).worldLaw ν) =
      ∫ ω, likelihood (fun i ↦ recenteredUnitScore (h i) θ) (2 * δ) ω.1 * F ω
        ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw ν := by
  rw [P.likelihoodWidePath_of_mem h hh hb hm hNew, P.likelihoodWidePath_of_mem h hh hb hm hθ]
  rw [← P.likelihoodWideTilt_rebase h hh hb hm hθ hδ hNew]
  exact (P.likelihoodWideTilt h hh hb hm θ hθ).integral_likelihoodTilt_worldLaw ν
    (fun i ↦ recenteredUnitScore (h i) θ) (fun i ↦ measurable_recenteredUnitScore (hh i) θ)
    (fun i ↦ recenteredUnitScore_bound (hb i) hθ)
    (fun i ↦ recenteredUnitScore_centered (hh i) (hb i) (hm i) hθ) hδ F

end ProphetSecretary.Model.Instance


namespace ProphetSecretary.Probability
open scoped BigOperators Topology
variable {n : ℕ}

lemma likelihood_abs_le_card {h : Fin n → ℝ → ℝ} {t : ℝ} {x : Fin n → ℝ}
    (ht : |t| ≤ 1 / 4) (hx : ∀ i, |h i (x i)| ≤ 1) :
    |likelihood h t x| ≤ (5 / 4 : ℝ) ^ n := by
  unfold likelihood
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin n, (5 / 4 : ℝ) := Finset.prod_le_prod
      (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ by
        have hi := tiltFactor_bounds ht (hx i)
        rw [abs_of_nonneg (by change 0 ≤ 1 + t * h i (x i); linarith [hi.1])]
        exact hi.2)
    _ = _ := by simp [div_pow]

lemma tendsto_likelihood_zero (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) :
    Filter.Tendsto (fun δ : ℝ ↦ likelihood h (2 * δ) x) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun δ : ℝ ↦ likelihood h (2 * δ) x) := by
    unfold likelihood tiltFactor
    fun_prop
  simpa only [mul_zero, likelihood_zero] using hc.tendsto 0

end ProphetSecretary.Probability
