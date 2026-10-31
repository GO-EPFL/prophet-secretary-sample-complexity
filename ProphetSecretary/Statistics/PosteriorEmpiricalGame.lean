import ProphetSecretary.Statistics.FinitePriorGameExpectation
import ProphetSecretary.Statistics.PosteriorEmpiricalBlockIndex
import ProphetSecretary.Model.EmpiricalTrainingBlockReach

/-!
# The actual posterior empirical learner in the reward/reach game

Deletion monotonicity is proved for this constructed learner. It is not
assumed for general competing policies. The hypothetical next posterior
is used only in the covariance bound, not by the training protocol or
online callback. Paper correspondence: `eq:bayes-target-score`.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

lemma posteriorEmpirical_meanDuration_le_reach (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (P : Instance n) (i : Fin n) :
    (F.posteriorEmpiricalLearner N b k
      (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ hρ).meanDuration P ≤
    (F.posteriorEmpiricalLearner N b k
      (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ hρ).reachProbability P i := by
  rw [F.posteriorEmpiricalLearner_eq_block N b k h ρ hρ]
  exact Learner.empiricalTrainingBlock_meanDuration_le_reach_under (Measure.dirac ())
    (empiricalBlockColumn b m (trainingLength N b k) h) (F.prefixPosteriorScalar N b k ρ)
    (F.measurable_prefixPosteriorScalar N b k hρ) P
    ((P.reservoirLaw (trainingLength N b k)).prod (Measure.dirac ())) i

theorem posteriorEmpirical_game_ge_posterior_score (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) (hk : b+k<N)
    (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) {C : ℝ} (hC : C∈Icc (0 : ℝ) 1) :
    (∫ w, F.onlineGameScore N b k
      (F.posteriorEmpiricalPolicy N b k
        (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ)
      C (F.posterior N b k) w ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod (Measure.dirac ())))-
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N) ≤
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        (F.posteriorEmpiricalLearner N b k
          (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ hρ).targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
  let e := empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))
  let π := F.posteriorEmpiricalPolicy N b k e ρ
  have hπ := F.posteriorEmpiricalPolicy_isMeasurable N b k e hρ
  have hBound := F.target_score_ge_posterior_score_sub_increment N b k hk hcap (Measure.dirac ()) π hπ hC
  rw [F.integral_trueTargetScore_eq_average N b k hcap (Measure.dirac ()) π hπ hC] at hBound
  apply hBound.trans
  apply Finset.sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left _ (F.weight θ).coe_nonneg
  exact (F.posteriorEmpiricalLearner N b k e ρ hρ).targetDurationPayoff_le_game
    (F.offerInstance θ) (F.target θ) C (fun i => F.posteriorEmpirical_meanDuration_le_reach N b k h ρ hρ (F.offerInstance θ) i)

end ProphetSecretary.Statistics.FinitePrior
