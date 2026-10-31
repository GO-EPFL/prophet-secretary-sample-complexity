import ProphetSecretary.Limiting.CountableMaskOrder
import ProphetSecretary.Limiting.HybridRetainedMonotonicityTerminal

/-!
# Mask monotonicity with an arbitrary terminal reserve

Finite zero-variable simulations preserve the reserve. The hybrid comparison
with reserve passes through the actual countable truncation value limits.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting

lemma CountableInstance.finiteMaskState_value_mono_with_terminal (B : CountableInstance)
    (N : ℕ) (b : ℝ) (hb : (B.terminal : ℝ) < b) (left right : IndividualMask) (hMasks : MaskLe left right)
    (u : ℝ≥0) {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    ((B.finiteMaskState N b hb (restrictIndividualMask N left)).remainingHorizon u).optimalScalarValue w d ≤
      ((B.finiteMaskState N b hb (restrictIndividualMask N right)).remainingHorizon u).optimalScalarValue w d := by
  let D := (B.truncation N b hb).remainingHorizon u
  let A := finiteMaskSet (restrictIndividualMask N left)
  let C := finiteMaskSet (restrictIndividualMask N right)
  have hAC : A ⊆ C := by
    intro i hi
    have hi' : left i.val = true := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hMasks i.val hi'⟩
  calc
    _ = (D.zeroOutside A).optimalScalarValue w d := B.finiteMaskState_value_eq_zeroOutside N b hb _ w d u
    _ = (D.restrictIndividuals A).optimalScalarValue w d := D.zeroOutside_value_eq_restrictIndividuals_with_terminal A hw hd
    _ ≤ (D.restrictIndividuals C).optimalScalarValue w d := D.optimalScalarValue_restrictIndividuals_mono_with_terminal hAC hw hd
    _ = (D.zeroOutside C).optimalScalarValue w d := (D.zeroOutside_value_eq_restrictIndividuals_with_terminal C hw hd).symm
    _ = _ := (B.finiteMaskState_value_eq_zeroOutside N b hb _ w d u).symm

theorem CountableInstance.remainingState_value_mono_mask_with_terminal (B : CountableInstance)
    (left right : IndividualMask) (hMasks : MaskLe left right) (u : ℝ≥0)
    {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    (B.remainingState left u).optimalScalarValue w d ≤ (B.remainingState right u).optimalScalarValue w d := by
  have hL := (B.remainingState left u).truncation_value_tendsto (fun N : ℕ => N) B.markCutoff
    B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hd
  have hR := (B.remainingState right u).truncation_value_tendsto (fun N : ℕ => N) B.markCutoff
    B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hd
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [] with N
  have hLeft := congrArg (fun D : FiniteIntensityHybridInstance N => D.optimalScalarValue w d)
    (B.remainingState_truncation_eq left u N (B.markCutoff N) (B.terminal_lt_markCutoff N))
  have hRight := congrArg (fun D : FiniteIntensityHybridInstance N => D.optimalScalarValue w d)
    (B.remainingState_truncation_eq right u N (B.markCutoff N) (B.terminal_lt_markCutoff N))
  exact hLeft.le.trans ((B.finiteMaskState_value_mono_with_terminal N (B.markCutoff N) (B.terminal_lt_markCutoff N)
    left right hMasks u hw hd).trans hRight.symm.le)

end ProphetSecretary.Limiting
