import ProphetSecretary.Limiting.FiniteBandNormalization
import ProphetSecretary.Limiting.CountableRemainingState
import ProphetSecretary.Limiting.CountablePoissonBands

/-!
# Actual band scaling of a locally finite limiting intensity

The density is r on the band and one on its complement. All individual laws,
identities and clocks are retained. The positive-level tail bound is proved
from the finite factor r+1, even when the total intensity is infinite.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def scaleBand (B : CountableInstance) (S : Set ℝ) (r : ℝ≥0) : CountableInstance where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individuals
  individual_supported := B.individual_supported
  intensity := B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x))
  intensity_supported := (withDensity_absolutelyContinuous _ _).ae_le B.intensity_supported
  individual_tail_finite := B.individual_tail_finite
  intensity_tail_finite b hb := by
    have hDom : B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x)) ≤
        ENNReal.ofReal ((r : ℝ)+1) • B.intensity := by
      calc
        _ ≤ B.intensity.withDensity (fun _ => ENNReal.ofReal ((r : ℝ)+1)) :=
          withDensity_mono (Eventually.of_forall (fun x => ENNReal.ofReal_le_ofReal (bandScaleFactor_le S r x)))
        _ = _ := withDensity_const _
    have hTail : (B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x))) (Ioi b) ≤
        (ENNReal.ofReal ((r : ℝ)+1) • B.intensity) (Ioi b) := hDom (Ioi b)
    rw [Measure.smul_apply,smul_eq_mul] at hTail
    exact hTail.trans_lt (ENNReal.mul_lt_top (by simp) (B.intensity_tail_finite b hb))

lemma scaleBand_one (B : CountableInstance) (S : Set ℝ) : B.scaleBand S 1=B := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · rfl
  · change B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S 1 x))=B.intensity
    have hFunction : (fun x => ENNReal.ofReal (bandScaleFactor S 1 x))=fun _ => (1 : ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ S <;> simp [bandScaleFactor,hx]
    rw [hFunction]
    change B.intensity.withDensity 1=B.intensity
    exact withDensity_one

lemma scaleBand_bandIntensity (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (r : ℝ≥0) (k : ℕ) :
    (B.scaleBand S r).bandIntensity k=bandScaledIntensity (B.bandIntensity k) S r := by
  apply FiniteMeasure.toMeasure_injective
  change (B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x))).restrict (B.markBand k)=_
  rw [restrict_withDensity (B.measurableSet_markBand k)]
  exact (bandScaledIntensity_toMeasure (B.bandIntensity k) hS r).symm

end ProphetSecretary.Limiting.CountableInstance
