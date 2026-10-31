import ProphetSecretary.Limiting.CountablePositiveTail

/-!
# A common positive-tail profile for all finite truncations
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

lemma truncation_tailCount_le (B : CountableInstance) (N : ℕ) {cut : ℝ}
    (hcut : (B.terminal : ℝ) < cut) (d : ℝ) (hd : (B.terminal : ℝ) < d) :
    (B.truncation N cut hcut).tailCount d ≤ B.positiveTailCount d hd := by
  have hSum : (∑ i : Fin N, (B.individuals i.val : Measure ℝ) (Ioi d)) ≤
      ∑' i, (B.individuals i : Measure ℝ) (Ioi d) := by
    calc
      _ = ∑ i ∈ Finset.range N, (B.individuals i : Measure ℝ) (Ioi d) :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ => (B.individuals i : Measure ℝ) (Ioi d)) N
      _ ≤ _ := ENNReal.sum_le_tsum (Finset.range N)
  have hInd := ENNReal.toReal_mono (B.individual_tail_finite d hd).ne hSum
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at hInd
  have hIndividuals : (B.truncation N cut hcut).individuals.tailCount d ≤
      (∑' i, (B.individuals i : Measure ℝ) (Ioi d)).toReal := hInd
  have hIntensity : ((B.truncation N cut hcut).intensity : Measure ℝ).real (Ioi d) ≤
      B.intensity.real (Ioi d) := by
    change ((B.intensity.restrict (Ioi cut)) (Ioi d)).toReal ≤ (B.intensity (Ioi d)).toReal
    rw [Measure.restrict_apply measurableSet_Ioi]
    exact ENNReal.toReal_mono (B.intensity_tail_finite d hd).ne (measure_mono inter_subset_left)
  change (B.truncation N cut hcut).individuals.tailCount d+
    ((B.truncation N cut hcut).intensity : Measure ℝ).real (Ioi d) ≤ _
  rw [B.positiveTailCount_eq d hd]
  exact add_le_add hIndividuals hIntensity

end ProphetSecretary.Limiting.CountableInstance
