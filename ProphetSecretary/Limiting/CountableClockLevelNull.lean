import ProphetSecretary.Limiting.CountableClockProfile
import ProphetSecretary.Limiting.Support

/-!
# Null level times of the actual changing-mask continuation profile

The proof follows the mask of arrivals as elapsed time increases. It does not
form a union over the uncountable space of all possible unseen masks.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma clockProfile_positive_level_subsingleton (B : CountableInstance) (hZero : B.terminal = 0)
    (clocks : ℕ → ℝ) (candidate : Option ℕ) {w c x : ℝ} (hw : 0 < w) (hc : 0 < c) (hx : 0 < x) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ B.clockProfile clocks candidate w c t = x}.Subsingleton := by
  intro t ht s hs
  have hNoLt (a b : ℝ) (haTime : a ∈ Icc (0 : ℝ) 1) (hbTime : b ∈ Icc (0 : ℝ) 1)
      (haValue : B.clockProfile clocks candidate w c a = x) (hbValue : B.clockProfile clocks candidate w c b = x) : ¬a < b := by
    intro hab
    have hSecant := B.clockProfile_secant hZero clocks candidate hw hc hx haTime.1 hab.le hbTime.2
      (show x ≤ B.clockProfile clocks candidate w c b by rw [hbValue])
    have hPos : 0 < c*B.continuationBandFloor hZero w c x hw hx*(b-a) :=
      mul_pos (mul_pos hc (B.continuationBandFloor_pos hZero hw hc hx)) (sub_pos.mpr hab)
    rw [haValue,hbValue,sub_self] at hSecant
    exact (not_le_of_gt hPos) hSecant
  exact le_antisymm (not_lt.mp (hNoLt s t hs.1 ht.1 hs.2 ht.2))
    (not_lt.mp (hNoLt t s ht.1 hs.1 ht.2 hs.2))

/-- Every fixed real level has null equality times under the actual uniform
clock law. Nonpositive levels are excluded by positive preterminal waiting. -/
theorem clockProfile_time_ne_ae (B : CountableInstance) (hZero : B.terminal = 0)
    (clocks : ℕ → ℝ) (candidate : Option ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (x : ℝ) :
    ∀ᵐ t ∂Model.Instance.uniformClock, B.clockProfile clocks candidate w c t ≠ x := by
  by_cases hx : 0 < x
  · have hNull := (B.clockProfile_positive_level_subsingleton hZero clocks candidate hw hc hx).countable.measure_zero
      Model.Instance.uniformClock
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNull,uniformClock_mem_Ioo] with t ht hTime
    intro hEq
    exact ht ⟨⟨hTime.1.le,hTime.2.le⟩,hEq⟩
  · filter_upwards [uniformClock_mem_Ioo] with t ht
    intro hEq
    have hPos := B.clockProfile_pos clocks candidate hw hc ht.2
    rw [hEq] at hPos
    exact (not_lt.mp hx).not_gt hPos

end ProphetSecretary.Limiting.CountableInstance
