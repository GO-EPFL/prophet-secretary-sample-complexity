import ProphetSecretary.Limiting.PositiveOfferIntensity
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Restricting actual finite positive-offer intensities to upper bands

For b≥0 the positive restriction at zero is redundant above b. The result is
the literal sum of the original marginal restrictions, with atoms at b excluded.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma positiveOfferIntensity_restrict_band (R : Model.Instance n) {b : ℝ} (hb : 0 ≤ b) :
    (positiveOfferIntensity R).restrict (Ioi b) =
      ∑ i, (R.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b) := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  change ((positiveOfferIntensity R : Measure ℝ).restrict (Ioi b)) E = _
  rw [Measure.restrict_apply hE,positiveOfferIntensity_toMeasure,Measure.finsetSum_apply,
    FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((R.law i).restrict (Ioi 0)) (E ∩ Ioi b) = ((R.law i).restrict (Ioi b)) E
  rw [Measure.restrict_apply (hE.inter measurableSet_Ioi),Measure.restrict_apply hE]
  congr 1
  exact inter_eq_left.mpr (fun _ hx => hb.trans_lt hx.2)

end ProphetSecretary.Limiting
