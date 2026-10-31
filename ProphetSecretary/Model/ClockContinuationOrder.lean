import ProphetSecretary.Model.ContinuationSlope
import ProphetSecretary.Probability.CensoredContinuation

/-!
# Order of true continuation values along the clock path

As elapsed time increases, the remaining horizon shrinks and the unseen
identity set decreases. This gives monotonicity for the actual value curve,
including its downward jumps and the terminal state. No zero-horizon value
identity is assumed.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma pendingClockSet_antitone (u : Fin n → ℝ) : Antitone (fun t => pendingClockSet t u) := by
  intro t s hts j hj
  apply (mem_pendingClockSet t u j).mpr
  exact hts.trans ((mem_pendingClockSet s u j).mp hj)

lemma Instance.clockContinuation_antitone (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) :
    AntitoneOn (fun t => P.continuationValue (pendingClockSet t u) (1 - t) 1 z) (Iic (1 : ℝ)) := by
  intro t ht s hs hts
  have hsub := pendingClockSet_antitone u hts
  calc
    P.continuationValue (pendingClockSet s u) (1 - s) 1 z ≤
        P.continuationValue (pendingClockSet s u) (1 - t) 1 z :=
      P.continuationValue_horizon_mono hP _ (sub_nonneg.mpr hs) (by linarith) zero_le_one hz
    _ ≤ P.continuationValue (pendingClockSet t u) (1 - t) 1 z :=
      P.optimalScalarValue_restrictTo_mono hP hsub zero_le_one (mul_nonneg hz (sub_nonneg.mpr ht))

/-- Fixing the smaller end state gives a lower bound on the value drop. This
absorbs all intervening variable deletions without summing jump derivatives. -/
lemma Instance.clockContinuation_drop_ge_endState (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z t s : ℝ} (hz : 0 ≤ z) (ht : t ≤ 1)
    (hts : t ≤ s) (u : Fin n → ℝ) :
    P.continuationValue (pendingClockSet s u) (1 - t) 1 z -
        P.continuationValue (pendingClockSet s u) (1 - s) 1 z ≤
      P.continuationValue (pendingClockSet t u) (1 - t) 1 z -
        P.continuationValue (pendingClockSet s u) (1 - s) 1 z := by
  have h := P.optimalScalarValue_restrictTo_mono hP (pendingClockSet_antitone u hts)
    zero_le_one (mul_nonneg hz (sub_nonneg.mpr ht))
  exact sub_le_sub_right h _

end ProphetSecretary.Model
