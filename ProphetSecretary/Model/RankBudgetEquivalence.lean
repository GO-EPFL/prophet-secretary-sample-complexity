import ProphetSecretary.Model.ClockLearnerToRank
import ProphetSecretary.Model.RankLearnerToClock
import ProphetSecretary.Model.RankCompetitiveRatio

/-!
# Equality of hard sample complexity in the rank and clock models

The same k works for every finite size. Each learner is fixed before its
instance law, both constructions are causal, and their training transcripts
and hard budgets are preserved on every outcome. Expected reward and reach
also agree after averaging all training and online randomness.
-/

open MeasureTheory

namespace ProphetSecretary.Model

/-- The random-order version of the paper's feasible hard sample budget. -/
def RankFeasibleBudget (eps : ℝ) (k : ℕ) : Prop :=
  ∃ learners : ∀ n : ℕ, RankLearner n k,
    ∀ n, (learners n).Guarantees (optimalRankCompetitiveRatio-eps)

theorem rankFeasibleBudget_iff (eps : ℝ) (k : ℕ) : RankFeasibleBudget eps k ↔ FeasibleBudget eps k := by
  rw [RankFeasibleBudget,FeasibleBudget,optimalRankCompetitiveRatio_eq]
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨fun n => (L n).rankToClock,fun n => ((L n).rankToClock_guarantees_iff _).mpr (hL n)⟩
  · rintro ⟨L,hL⟩
    exact ⟨fun n => (L n).clockToRank,fun n => ((L n).clockToRank_guarantees_iff _).mpr (hL n)⟩

noncomputable def rankSampleComplexity (eps : ℝ) : ℕ∞ :=
  sInf {b : ℕ∞ | ∃ k : ℕ, RankFeasibleBudget eps k ∧ b = k}

theorem rankSampleComplexity_eq (eps : ℝ) : rankSampleComplexity eps = sampleComplexity eps := by
  simp only [rankSampleComplexity,sampleComplexity,rankFeasibleBudget_iff]

end ProphetSecretary.Model
