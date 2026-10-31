import ProphetSecretary.Model.ClockLearnerToRank
import ProphetSecretary.Model.RankLearnerToClock

/-!
# Fixed-value decisions are preserved by the causal model transports

In particular, accepting caps and rejecting zero on every raw history survive
both directions, even on seed or training outcomes of probability zero.
-/

namespace ProphetSecretary.Model

variable {n k : ℕ}

lemma Learner.clockToRank_fixedAction (L : Learner n k) (v : ℝ) (b : Bool)
    (h : ∀ y r t i H, L.policy.decide (y,r) t i v H=b)
    (y : Reservoir n k) (sr : (Fin n → ℝ) × L.Seed) (q i : Fin n) (H : RankHistory n) :
    L.clockToRank.policy.decide (y,sr) q i v H=b := by
  rcases sr with ⟨s,r⟩
  change L.decide r (trainingTranscript L.clockToRank.request (s,r) y) (s q) i v _=b
  rw [L.clockToRank_trainingTranscript]
  exact h y r (s q) i (fun j => (H j).map (fun a => (s a.1,a.2)))

lemma RankLearner.rankToClock_fixedAction (L : RankLearner n k) (v : ℝ) (b : Bool)
    (h : ∀ y r q i H, L.policy.decide (y,r) q i v H=b)
    (y : Reservoir n k) (r : L.Seed) (t : ℝ) (i : Fin n) (H : History n) :
    L.rankToClock.policy.decide (y,r) t i v H=b := by
  change L.policy.decide (y,r) (currentRankFromClock i H) i v (rankHistoryFromClock i H)=b
  exact h y r _ i _

end ProphetSecretary.Model
