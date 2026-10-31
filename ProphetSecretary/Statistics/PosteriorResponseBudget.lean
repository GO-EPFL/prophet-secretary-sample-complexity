import ProphetSecretary.Statistics.BudgetGamePerformance
import ProphetSecretary.Model.NonnegativeTimeGuard
import ProphetSecretary.Statistics.PosteriorEmpiricalLearner
import ProphetSecretary.Statistics.PosteriorEmpiricalBlockIndex

/-!
# A common hard budget for posterior responses

A deployment index k<3m is fixed before training. Its actual empirical
response is extended at negative raw times and padded to the common 3m
budget. Reward and each reach probability are preserved; the endpoint
actions hold on every raw input used by the finite strategy representation.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ}

lemma Learner.guardNegativeTimes_targetGamePayoff (L : Learner n k) (P : Instance n)
    (J : Option (Fin n)) (C : ℝ) :
    L.guardNegativeTimes.targetGamePayoff P J C=L.targetGamePayoff P J C := by
  cases J with
  | none => exact congrArg (fun r => r-C*P.expectedMaximum) (L.guardNegativeTimes_expectedReward P)
  | some i => exact congrArg (fun q => q-C) (L.guardNegativeTimes_reachProbability P i)

end ProphetSecretary.Model
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m : ℕ} [NeZero m]

noncomputable def budgetedPosteriorResponse (F : FinitePrior n) (k : ℕ)
    (beta : ℝ) : Learner n (3*m) :=
  ((F.posteriorEmpiricalLearner (3*m) 0 k
    (empiricalBlockColumn 0 m (3*m+1) (by omega))
    (fun lam => max (4/5) (min beta lam))
    (measurable_const.max (measurable_const.min measurable_id))).guardNegativeTimes).padBudget
      (trainingLength_le (3*m) 0 k)

lemma budgetedPosteriorResponse_targetGamePayoff (F : FinitePrior n) (k : ℕ) (beta : ℝ)
    (P : Instance n) (J : Option (Fin n)) (C : ℝ) :
    (F.budgetedPosteriorResponse (m:=m) k beta).targetGamePayoff P J C=
      (F.posteriorEmpiricalLearner (3*m) 0 k
        (empiricalBlockColumn 0 m (3*m+1) (by omega))
        (fun lam => max (4/5) (min beta lam))
        (measurable_const.max (measurable_const.min measurable_id))).targetGamePayoff P J C := by
  unfold budgetedPosteriorResponse
  rw [Learner.padBudget_targetGamePayoff,Learner.guardNegativeTimes_targetGamePayoff]

lemma budgetedPosteriorResponse_accepts_cap (F : FinitePrior n) (k : ℕ) {beta : ℝ}
    (hBeta : beta∈Ioo (4/5 : ℝ) 1)
    (y : Reservoir n (3*m)) (r : (F.budgetedPosteriorResponse (m:=m) k beta).Seed)
    (t : ℝ) (i : Fin n) (H : History n) :
    (F.budgetedPosteriorResponse (m:=m) k beta).policy.decide (y,r) t i 1 H=true := by
  unfold budgetedPosteriorResponse
  rw [Learner.padBudget_decide]
  apply Learner.guardNegativeTimes_accepts_cap
  intro y r t ht i H
  exact F.posteriorEmpiricalLearner_accepts_cap (3*m) 0 k
    (empiricalBlockColumn 0 m (3*m+1) (by omega))
    (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id)) hBeta.2
    (fun lam hUnit => by
      refine ⟨le_max_left _ _,max_le hBeta.1.le (min_le_left _ _)⟩) y r ht i H

lemma budgetedPosteriorResponse_rejects_zero (F : FinitePrior n) (k : ℕ) (beta : ℝ)
    (y : Reservoir n (3*m)) (r : (F.budgetedPosteriorResponse (m:=m) k beta).Seed)
    (t : ℝ) (i : Fin n) (H : History n) :
    (F.budgetedPosteriorResponse (m:=m) k beta).policy.decide (y,r) t i 0 H=false := by
  unfold budgetedPosteriorResponse
  rw [Learner.padBudget_decide]
  apply Learner.guardNegativeTimes_rejects_zero
  intro y r t i H
  exact F.posteriorEmpiricalLearner_rejects_zero (3*m) 0 k
    (empiricalBlockColumn 0 m (3*m+1) (by omega))
    (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id)) y r t i H

end ProphetSecretary.Statistics.FinitePrior
