import ProphetSecretary.Statistics.MixedClockGapLoss
import ProphetSecretary.Statistics.EmpiricalClockLossBounds

/-!
# Common auxiliary bounds for actual mixed clock losses

A cap-one sample event bounds both directions for every scalar in the prescribed
interval, every candidate value and every nonnegative time. Exact known laws
satisfy the same cap support. The bound licenses Fubini and is separate from the
sharper statistical rate.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

/-- Every real array is accepted; its upper bound is an explicit hypothesis,
which is subsequently supplied almost surely by the actual sample law. -/
theorem paired_mixedClockGapLoss_bounded (P : Instance n) (known : Finset (Fin n))
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (y : Reservoir n k) (hy : ∀ j l, y j l≤1)
    {z hi t : ℝ} (hz : 0≤z) (hzhi : z≤hi) (ht : 0≤t) (u : Fin n → ℝ) (x : ℝ) :
    mixedClockGapLoss P known y z u x t ≤ 2+2*hi ∧ trueClockGapLossMixedEval P known y z u x t ≤ 2+2*hi := by
  have hPt := P.clockContinuation_mem_bound hPbound hz hzhi ht u
  have hQt := (mixedEmpiricalInstance P known y).clockContinuation_mem_bound
    (mixedEmpiricalInstance_bounded P known y zero_le_one hPbound hy) hz hzhi ht u
  let E := |P.clockContinuation z u t-(mixedEmpiricalInstance P known y).clockContinuation z u t|
  have hE0 : 0≤E := abs_nonneg _
  have hE : E≤2+2*hi := by
    dsimp [E]
    rw [abs_le]
    constructor <;> linarith only [hPt.1,hPt.2,hQt.1,hQt.2]
  have hb := paired_mixedClockGapLoss_bound P known y z u x t E le_rfl
  have hband : (if |x-P.clockContinuation z u t|≤E then E else 0)≤E := by
    split_ifs
    · exact le_rfl
    · exact hE0
  exact ⟨hb.1.trans (hband.trans hE),hb.2.trans (hband.trans hE)⟩

/-- The same training event supports every scalar, clock path, candidate value
and nonnegative time. There is no exceptional set in the learner's budget. -/
theorem Instance.paired_mixedClockGapLoss_bounded_ae (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hi : ℝ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ z∈Icc (0:ℝ) hi, ∀ u : Fin n → ℝ, ∀ x t : ℝ, 0≤t →
      mixedClockGapLoss P known (reservoirCoordinates.symm a) z u x t ≤ 2+2*hi ∧
        trueClockGapLossMixedEval P known (reservoirCoordinates.symm a) z u x t ≤ 2+2*hi := by
  filter_upwards [P.trainingCoordinates_bounded (k:=k) hbound] with a ha
  intro z hz u x t ht
  exact paired_mixedClockGapLoss_bounded P known hbound (reservoirCoordinates.symm a) ha hz.1 hz.2 ht u x

end ProphetSecretary.Model
