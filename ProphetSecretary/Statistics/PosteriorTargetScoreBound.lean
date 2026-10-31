import ProphetSecretary.Statistics.PosteriorEmpiricalGame
import ProphetSecretary.Statistics.PosteriorEmpiricalClampedScore
import ProphetSecretary.Statistics.ObservablePrefixScore

/-!
# The posterior-target score bound for the implemented learner

The interval's clamp is supplied by the already proved small-mean theorem.
The prior expectation averages the actual prefix training law under each
true atom. The covariance term is the next posterior increment, which is
analytical and never queried by the learner. This is the quantitative step
`eq:bayes-target-score`, before choosing a deployment index.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

noncomputable def expectedPosteriorGap (F : FinitePrior n) (N b k : ℕ) : ℝ :=
  ∑ θ : Fin F.size, (F.weight θ : ℝ)*
    (∫ p : Reservoir n (trainingLength N b k) × Unit,
      normalizedScalarGap (F.offerInstance θ)
        (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
      ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod (Measure.dirac ()))

noncomputable def posteriorEmpiricalError (F : FinitePrior n) (lo : ℝ) (m : ℕ) : ℝ :=
  ∑ θ : Fin F.size, (F.weight θ : ℝ)*
    (empiricalCapRegretConstant lo*(1+(F.offerInstance θ).totalFirstMoment*
      (1+(F.offerInstance θ).totalFirstMoment))/(m : ℝ))

theorem posteriorEmpirical_game_lower_bound (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) (hk : b+k<N) {beta : ℝ} (hBeta : beta∈Ioo (4/5 : ℝ) 1)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (hSmall : ∀ θ, (F.offerInstance θ).expectedMaximum≤1/80)
    (hClamp : ∀ θ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0 : ℝ) 1 →
      π.normalizedRegret (F.offerInstance θ) (max (4/5) (min beta lam))≤r →
      normalizedScalarGap (F.offerInstance θ) lam/40-5*r≤
        π.scalarObjective (F.offerInstance θ) lam (1-lam)-
          optimalCompetitiveRatio*(lam*(F.offerInstance θ).expectedMaximum+1-lam)) :
    F.expectedPosteriorGap N b k/40-5*F.posteriorEmpiricalError (1-beta) m-
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N) ≤
    ∑ θ : Fin F.size, (F.weight θ : ℝ)*
      (F.posteriorEmpiricalLearner N b k
        (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N))))
        (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id))).targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio := by
  let rho := fun lam : ℝ => max (4/5 : ℝ) (min beta lam)
  have hRho : Measurable rho := measurable_const.max (measurable_const.min measurable_id)
  let e := empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))
  let π := F.posteriorEmpiricalPolicy N b k e rho
  have hπ := F.posteriorEmpiricalPolicy_isMeasurable N b k e hRho
  have hC : optimalCompetitiveRatio∈Icc (0 : ℝ) 1 :=
    ⟨optimalCompetitiveRatio_nonnegative,optimalCompetitiveRatio_le_one⟩
  have hGame := F.posteriorEmpirical_game_ge_posterior_score N b k h hk rho hRho hcap hC
  rw [F.integral_currentPosteriorScore_eq_frozen_average N b k hcap (Measure.dirac ()) π hπ hC] at hGame
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun θ _ =>
    mul_le_mul_of_nonneg_left
      (F.posteriorEmpirical_frozen_score_lower N b k h hBeta (F.offerInstance θ) (hcap θ) (hSmall θ) (hClamp θ))
      (F.weight θ).coe_nonneg)
  have hLeft : (∑ θ : Fin F.size, (F.weight θ : ℝ)*
      ((∫ p : Reservoir n (trainingLength N b k) × Unit,
        normalizedScalarGap (F.offerInstance θ)
          (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
        ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod (Measure.dirac ()))/40-
      5*(empiricalCapRegretConstant (1-beta)*(1+(F.offerInstance θ).totalFirstMoment*
        (1+(F.offerInstance θ).totalFirstMoment))/(m : ℝ)))) =
      F.expectedPosteriorGap N b k/40-5*F.posteriorEmpiricalError (1-beta) m := by
    unfold expectedPosteriorGap posteriorEmpiricalError
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro θ _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro θ _
      ring
  rw [hLeft] at hSum
  let L := F.posteriorEmpiricalLearner N b k e rho hRho
  let score := fun θ : Fin F.size =>
    ∫ p : Reservoir n (trainingLength N b k) × Unit,
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective (F.offerInstance θ)
        (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
        (1-F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))-
      optimalCompetitiveRatio*(F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)*
        (F.offerInstance θ).expectedMaximum+1-F.boundedPosteriorFromObservation N b k
          (extendTrainingPrefix n N b k p.1))
      ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod (Measure.dirac ())
  let payoff := ∑ θ : Fin F.size, (F.weight θ : ℝ)*L.targetGamePayoff
    (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio
  change (∑ θ : Fin F.size, (F.weight θ : ℝ)*score θ)-
    Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N)≤payoff at hGame
  change F.expectedPosteriorGap N b k/40-5*F.posteriorEmpiricalError (1-beta) m≤
    ∑ θ : Fin F.size, (F.weight θ : ℝ)*score θ at hSum
  change F.expectedPosteriorGap N b k/40-5*F.posteriorEmpiricalError (1-beta) m-
    Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N)≤payoff
  exact (sub_le_sub_right hSum _).trans hGame

end ProphetSecretary.Statistics.FinitePrior
