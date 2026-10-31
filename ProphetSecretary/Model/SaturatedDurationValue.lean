import ProphetSecretary.Model.CrossingRoots

/-!
# A continuous duration-value extension

`V(P;1,max(0,d))` is globally continuous and one-Lipschitz. At every positive
coefficient it has the actual canonical duration derivative. The extension is
constant below zero; no differentiability at zero is asserted.
-/

open MeasureTheory Set
open scoped Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.saturatedDurationValue (P : Instance n) (d : ℝ) : ℝ :=
  optimalScalarValue P 1 (max 0 d)

lemma Instance.saturatedDurationValue_continuous (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : Continuous P.saturatedDurationValue := by
  exact (optimalScalarValue_durationWeight_continuousOn P hP zero_le_one).comp_continuous
    (continuous_const.max continuous_id) (fun d ↦ by
      change (0 : ℝ) ≤ max 0 d
      exact le_max_left 0 d)

lemma Instance.saturatedDurationValue_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : LipschitzWith 1 P.saturatedDurationValue := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro d e
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  have h := optimalScalarValue_durationWeight_lipschitz P hP (w := 1) zero_le_one
    (le_max_left 0 d) (le_max_left 0 e)
  have hm : |max 0 d - max 0 e| ≤ |d - e| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (d - e))] using
      (abs_max_sub_max_le_max (0 : ℝ) d 0 e)
  exact h.trans hm

lemma Instance.saturatedDurationValue_hasDerivAt (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {d : ℝ} (hd : 0 < d) :
    HasDerivAt P.saturatedDurationValue
      ((P.valuePolicy hP (w := 1) (c := d) zero_le_one hd.le).expectedDuration P) d := by
  have h := remainingScalarValue_hasDerivAt P hP (w := 1) (c := 1) zero_lt_one zero_le_one hd
  have hplain : HasDerivAt (fun v ↦ optimalScalarValue P 1 v)
      ((P.valuePolicy hP (w := 1) (c := d) zero_le_one hd.le).expectedDuration P) d := by
    have heq : remainingScalarValue P 1 1 = (fun v ↦ optimalScalarValue P 1 v) := by
      funext v
      simp only [remainingScalarValue, one_mul]
    rw [heq] at h
    simpa only [one_mul] using h
  apply hplain.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hd] with v hv
  exact congrArg (optimalScalarValue P 1) (max_eq_right hv.le)

/-- Every positive coefficient is a strict level of the saturated value. -/
lemma Instance.saturatedDurationValue_level_iff (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {d : ℝ} (hd : 0 < d) (s : ℝ) :
    P.saturatedDurationValue s ≤ P.saturatedDurationValue d ↔ s ≤ d := by
  by_cases hs : 0 ≤ s
  · unfold Instance.saturatedDurationValue
    rw [max_eq_right hs, max_eq_right hd.le]
    constructor
    · intro h
      by_contra hn
      have hl := P.rewardNormalized_strictMonoOn hP hd.le hs (lt_of_not_ge hn)
      exact not_lt_of_ge h hl
    · intro h
      exact (P.rewardNormalized_strictMonoOn hP).monotoneOn hs hd.le h
  · have hs0 : s < 0 := lt_of_not_ge hs
    unfold Instance.saturatedDurationValue
    rw [max_eq_left hs0.le, max_eq_right hd.le]
    have hl := P.rewardNormalized_strictMonoOn hP (le_rfl : (0 : ℝ) ≤ 0) hd.le hd
    exact iff_of_true hl.le (hs0.le.trans hd.le)

lemma Instance.saturatedDurationValue_root (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ}
    (hx : optimalScalarValue P 1 0 < x) :
    P.saturatedDurationValue (P.durationRoot hP x) = x := by
  unfold Instance.saturatedDurationValue
  rw [max_eq_right (P.durationRoot_nonnegative hP x), P.durationRoot_value hP hx]

end ProphetSecretary.Model
