import ProphetSecretary.Model.ScalarSupport
import ProphetSecretary.Model.ContinuationODE

/-!
# Saturated duration coefficients with a positive reward weight

The continuation value is extended constantly below coefficient zero. The
extension is globally one-Lipschitz and has the actual coefficient derivative
at every positive coefficient. No differentiability at zero is asserted.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.weightedSaturatedValue (P : Instance n) (w d : ℝ) : ℝ :=
  optimalScalarValue P w (max 0 d)

lemma Instance.weightedSaturatedValue_continuous (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w : ℝ} (hw : 0 ≤ w) :
    Continuous (P.weightedSaturatedValue w) :=
  (optimalScalarValue_durationWeight_continuousOn P hP hw).comp_continuous
    (continuous_const.max continuous_id) (fun d ↦ le_max_left 0 d)

lemma Instance.weightedSaturatedValue_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w : ℝ} (hw : 0 ≤ w) :
    LipschitzWith 1 (P.weightedSaturatedValue w) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro d e
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  have h := optimalScalarValue_durationWeight_lipschitz P hP hw (le_max_left 0 d) (le_max_left 0 e)
  have hm : |max 0 d - max 0 e| ≤ |d - e| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (d - e))] using abs_max_sub_max_le_max (0 : ℝ) d 0 e
  exact h.trans hm

lemma Instance.weightedSaturatedValue_hasDerivAt (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w d : ℝ} (hw : 0 < w) (hd : 0 < d) :
    HasDerivAt (P.weightedSaturatedValue w) (deriv (remainingScalarValue P w 1) d) d := by
  have h := (remainingScalarValue_differentiableAt_all P hP hw zero_le_one hd).hasDerivAt
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hd] with v hv
  simp only [Instance.weightedSaturatedValue, max_eq_right (show (0 : ℝ) ≤ v from Ioi_subset_Ici_self hv), remainingScalarValue, one_mul]

lemma Instance.weightedSaturatedValue_level_iff (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) (s : ℝ) :
    P.weightedSaturatedValue w s ≤ P.weightedSaturatedValue w d ↔ s ≤ d := by
  constructor
  · intro h
    by_contra hn
    have hds : d < s := lt_of_not_ge hn
    have hs : 0 < s := hd.trans_lt hds
    have hg := P.remainingHorizon_growth hP (w := w) (c := 1) hw zero_le_one hd hds.le
    have hp : 0 < (1 / (4 * (1 + (n : ℝ)))) * (s - d) := mul_pos (by positivity) (sub_pos.mpr hds)
    simp only [Instance.weightedSaturatedValue, max_eq_right hs.le, max_eq_right hd] at h
    simp only [one_mul] at hg
    linarith
  · intro h
    have hmax : max 0 s ≤ d := max_le hd h
    exact (optimalScalarValue_mono P hP hw.le (le_max_left 0 s) le_rfl hmax).trans_eq
      (by simp only [Instance.weightedSaturatedValue, max_eq_right hd])

lemma Instance.weightedSaturatedValue_mul_remaining (P : Instance n) (w : ℝ) {c : ℝ}
    (hc : 0 ≤ c) (t : ℝ) :
    P.weightedSaturatedValue w (c * (1 - t)) = optimalScalarValue P w (c * max 0 (1 - t)) := by
  unfold Instance.weightedSaturatedValue
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

end ProphetSecretary.Model
