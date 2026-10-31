import ProphetSecretary.Statistics.CandidateGapFactorization
import ProphetSecretary.Statistics.MixedStateFutureErrorTransfer
import ProphetSecretary.Statistics.MixedClockGapLoss

/-!
# Exact candidate exclusion for mixed canonical losses

Restriction retains every other identity and pulls back the declared known labels.
The candidate's sample row is absent from its continuation in both directions.
These pointwise identities hold on every real training array before any product-law
averaging, and the candidate value/time remain independent analytical inputs.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

theorem mixedCanonicalCandidateLoss_eq_otherLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    (a : (Fin n × Fin k) → ℝ) {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) :
    canonicalCandidateLoss (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) P
      (mixedEmpiricalInstance_integrable P hP known _) z hz i u x t =
      mixedClockGapLoss (P.restrictTo (Finset.univ.erase i)) (knownInState known (Finset.univ.erase i))
        (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a))
        z (u ∘ stateEmbedding (Finset.univ.erase i)) x t := by
  rw [canonicalCandidateLoss_eq_otherGaps _ P (mixedEmpiricalInstance_integrable P hP known _) hP hz i u x t,
    mixedEmpiricalInstance_restrictTo_coordinates]
  rfl

theorem trueCanonicalCandidateLoss_mixedTarget_eq_otherLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    (a : (Fin n × Fin k) → ℝ) {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) :
    canonicalCandidateLoss P (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) hP z hz i u x t =
      trueClockGapLossMixedEval (P.restrictTo (Finset.univ.erase i)) (knownInState known (Finset.univ.erase i))
        (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a))
        z (u ∘ stateEmbedding (Finset.univ.erase i)) x t := by
  rw [canonicalCandidateLoss_eq_otherGaps P _ hP (mixedEmpiricalInstance_integrable P hP known _) hz i u x t,
    mixedEmpiricalInstance_restrictTo_coordinates]
  rfl

end ProphetSecretary.Model
