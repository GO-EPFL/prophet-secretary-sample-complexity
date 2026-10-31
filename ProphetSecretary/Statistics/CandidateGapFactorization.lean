import ProphetSecretary.Statistics.CanonicalCandidateLoss
import ProphetSecretary.Statistics.CandidateContinuationFactorization
import ProphetSecretary.Model.ClockNearLoss

/-!
# Local candidate loss is a gap of the other-variable clock continuations

The candidate's own offer law and sample row are absent from both continuation
curves. Its independent value is the explicit scalar x, and a selected z is a
separate fixed parameter. This is the factorization used before integrating
candidate values and averaging empirical candidate laws at a fixed weight.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem canonicalCandidateLoss_eq_otherGaps (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) :
    canonicalCandidateLoss Q P hQ z hz i u x t =
      ProphetSecretary.Analysis.gapLoss
        (decide (0≤x-(Q.restrictTo (Finset.univ.erase i)).clockContinuation z (u ∘ stateEmbedding (Finset.univ.erase i)) t))
        (x-(P.restrictTo (Finset.univ.erase i)).clockContinuation z (u ∘ stateEmbedding (Finset.univ.erase i)) t) := by
  unfold canonicalCandidateLoss
  rw [Q.valuePolicy_arrivalLoss_eq_gapLoss P hQ hz _ _ i]
  rw [Function.update_self,
    Q.continuationAtArrival_values_invariant 1 z (Function.update (fun _ => 0) i x) (fun _ => 0) (Function.update u i t) i,
    P.continuationAtArrival_values_invariant 1 z (Function.update (fun _ => 0) i x) (fun _ => 0) (Function.update u i t) i,
    Q.continuationAtArrival_eq_otherPending hQ hz (fun _ => 0) u i t,
    P.continuationAtArrival_eq_otherPending hP hz (fun _ => 0) u i t]
  rfl

/-- In the empirical design curve, projection to the other rows is exact on
EVERY real sample array, before any averaging or independence is used. -/
theorem empiricalCanonicalCandidateLoss_eq_otherGaps {k : ℕ} [NeZero k] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) :
    canonicalCandidateLoss (totalEmpiricalInstance (reservoirCoordinates.symm a)) P
      (totalEmpiricalInstance_integrable _) z hz i u x t =
      ProphetSecretary.Analysis.gapLoss
        (decide (0≤x-(totalEmpiricalInstance (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a))).clockContinuation
          z (u ∘ stateEmbedding (Finset.univ.erase i)) t))
        (x-(P.restrictTo (Finset.univ.erase i)).clockContinuation z (u ∘ stateEmbedding (Finset.univ.erase i)) t) := by
  rw [canonicalCandidateLoss_eq_otherGaps _ P (totalEmpiricalInstance_integrable _) hP hz i u x t,
    totalEmpiricalInstance_restrictTo_coordinates]

/-- Reverse evaluation for the fixed true optimizer, before the separate
fixed-weight unbiasedness argument used for upward bias. -/
theorem trueCanonicalCandidateLoss_empiricalEval_eq_otherGaps {k : ℕ} [NeZero k] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) :
    canonicalCandidateLoss P (totalEmpiricalInstance (reservoirCoordinates.symm a)) hP z hz i u x t =
      ProphetSecretary.Analysis.gapLoss
        (decide (0≤x-(P.restrictTo (Finset.univ.erase i)).clockContinuation z (u ∘ stateEmbedding (Finset.univ.erase i)) t))
        (x-(totalEmpiricalInstance (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a))).clockContinuation
          z (u ∘ stateEmbedding (Finset.univ.erase i)) t) := by
  rw [canonicalCandidateLoss_eq_otherGaps P _ hP (totalEmpiricalInstance_integrable _) hz i u x t,
    totalEmpiricalInstance_restrictTo_coordinates]

end ProphetSecretary.Model
