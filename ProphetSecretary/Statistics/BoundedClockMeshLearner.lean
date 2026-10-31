import ProphetSecretary.Statistics.BoundedGridMesh
import ProphetSecretary.Model.RankValueActions

/-!
# The bounded finite-program learner in the clock model

Causal rank-to-clock transport preserves the actual reward, reach, training
transcript and every-outcome cap/zero rules. The policy class of the clock
model remains unrestricted. Its rate lower bound is supplied separately by
the statistical Bayes-response argument.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def boundedClockMeshLearner (m : ℕ) (G : Finset ℝ)
    (hG : ∀ x∈G, 0≤x) (μ μhi ℓ : ℝ) : Learner n k :=
  (boundedMeshLearner (n:=n) (k:=k) m G hG μ μhi ℓ).rankToClock

lemma boundedClockMeshLearner_requests_eq (m : ℕ) (G : Finset ℝ)
    (hG : ∀ x∈G, 0≤x) (μ μhi ℓ : ℝ) (y : Reservoir n k) (T : RankStrategyTable n k G) (i : Fin n) :
    requests (trainingTranscript (boundedClockMeshLearner m G hG μ μhi ℓ).request T y) i=k := by
  exact boundedGridLearner_requests_eq G hG (boundedGridMeshDenominator_positive n k m G μ) (μ/2) μhi ℓ y T i

lemma boundedClockMeshLearner_accepts_cap (m : ℕ) (G : Finset ℝ)
    (hG : ∀ x∈G, 0≤x) (μ μhi ℓ : ℝ) (y : Reservoir n k) (T : RankStrategyTable n k G)
    (t : ℝ) (i : Fin n) (H : History n) :
    (boundedClockMeshLearner m G hG μ μhi ℓ).policy.decide (y,T) t i 1 H=true :=
  RankLearner.rankToClock_fixedAction (boundedMeshLearner (n:=n) (k:=k) m G hG μ μhi ℓ) 1 true
    (boundedGridLearner_accepts_cap G hG _ (μ/2) μhi ℓ) y T t i H

lemma boundedClockMeshLearner_rejects_zero (m : ℕ) (G : Finset ℝ)
    (hG : ∀ x∈G, 0≤x) (μ μhi ℓ : ℝ) (y : Reservoir n k) (T : RankStrategyTable n k G)
    (t : ℝ) (i : Fin n) (H : History n) :
    (boundedClockMeshLearner m G hG μ μhi ℓ).policy.decide (y,T) t i 0 H=false :=
  RankLearner.rankToClock_fixedAction (boundedMeshLearner (n:=n) (k:=k) m G hG μ μhi ℓ) 0 false
    (boundedGridLearner_rejects_zero G hG _ (μ/2) μhi ℓ) y T t i H

theorem boundedClockMeshLearner_guarantees_at_rate {m : ℕ} (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hz : (0 : ℝ)∈G)
    (hm : 0<m) {μ : ℝ} (hμ : 0<μ) (μhi ℓ : ℝ) (P : Instance n)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (hMean : μ≤P.expectedMaximum)
    (hUpper : P.expectedMaximum≤μhi) (hCount : P.positiveCount≤ℓ) :
    boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ*P.expectedMaximum-1/(m : ℝ)^2 ≤
      (boundedClockMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).expectedReward P ∧
    ∀ i, boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ-1/(m : ℝ)^2 ≤
      (boundedClockMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).reachProbability P i := by
  simpa only [boundedClockMeshLearner,RankLearner.rankToClock_expectedReward,
    RankLearner.rankToClock_reachProbability] using
    boundedMeshLearner_guarantees_at_rate (k:=k) G hBound hz hm hμ μhi ℓ P hG hMean hUpper hCount

end ProphetSecretary.Statistics
