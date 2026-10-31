import ProphetSecretary.Model.ExcessOrder
import ProphetSecretary.Model.ExcessMeasure

/-!
# Positive tails of excess offers

For nonnegative reserve a and level b, the excess tail above b is the original
tail above a+b. The actual measure pushforward proves this identity, including
atoms at the reserve and at the tested level.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

lemma excessValueMap_positive_iff {a x : ℝ} (ha : 0 ≤ a) : 0 < excessValueMap a x ↔ a < x := by
  constructor
  · intro hx
    have he := positive_excess_reconstructs_value ha hx
    linarith only [he,hx]
  · intro hx
    have hxp : 0 ≤ x := ha.trans hx.le
    unfold excessValueMap
    rw [max_eq_left hxp,min_eq_left hx.le]
    exact sub_pos.mpr hx

lemma excessValueMap_gt_iff {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b < excessValueMap a x ↔ a + b < x := by
  constructor
  · intro hx
    have hp := hb.trans_lt hx
    have he := positive_excess_reconstructs_value ha hp
    linarith only [he,hx]
  · intro hx
    have hax : a < x := (le_add_of_nonneg_right hb).trans_lt hx
    have hp := (excessValueMap_positive_iff ha).mpr hax
    have he := positive_excess_reconstructs_value ha hp
    linarith only [he,hx]

lemma excessLaw_positiveTail (κ : Measure ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    excessLaw κ a (Ioi b) = κ (Ioi (a + b)) := by
  rw [excessLaw,Measure.map_apply (measurable_excessValueMap a) measurableSet_Ioi]
  congr 1
  ext x
  exact excessValueMap_gt_iff ha hb

lemma excessLaw_positiveProbability_le (κ : Measure ℝ) [IsFiniteMeasure κ] {a : ℝ} (ha : 0 ≤ a) :
    (excessLaw κ a).real (Ioi 0) ≤ κ.real (Ioi 0) := by
  have he := excessLaw_positiveTail κ ha (show (0 : ℝ) ≤ 0 from le_rfl)
  simp only [add_zero] at he
  unfold Measure.real
  rw [he]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun _ hx => ha.trans_lt hx))

end ProphetSecretary.Model
