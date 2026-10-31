import ProphetSecretary.Limiting.HybridValueThreshold
import ProphetSecretary.Limiting.Support

/-!
# Null positive continuation-level times

Strict remaining-horizon secants imply that a fixed positive continuation
level is attained at at most one physical time in [0,1]. Countability of the
finite retained-state family then makes every fixed mark's threshold equality
null under the actual independent uniform clock, even for atomic mark laws.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.continuationTime_positive_level_subsingleton
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c x : ℝ} (hw : 0 < w) (hc : 0 < c) (hx : 0 < x) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ B.continuationValue w c (remainingTime t) = x}.Subsingleton := by
  intro t ht s hs
  have hNoLt (a b : ℝ) (haTime : a ∈ Icc (0 : ℝ) 1) (hbTime : b ∈ Icc (0 : ℝ) 1)
      (hfa : B.continuationValue w c (remainingTime a) = x)
      (hfb : B.continuationValue w c (remainingTime b) = x) : ¬a < b := by
    intro hab
    have hRem : remainingTime b < remainingTime a := by
      have hR : (remainingTime b : ℝ) < (remainingTime a : ℝ) := by
        rw [coe_remainingTime hbTime.2,coe_remainingTime haTime.2]
        linarith
      exact_mod_cast hR
    have hStrict := B.continuationValue_lt_of_lt ha hw hc hx hRem
      (remainingTime_le_one haTime.1) (show x ≤ B.continuationValue w c (remainingTime b) by rw [hfb])
    rw [hfa,hfb] at hStrict
    exact lt_irrefl x hStrict
  exact le_antisymm (not_lt.mp (hNoLt s t hs.1 ht.1 hs.2 ht.2))
    (not_lt.mp (hNoLt t s ht.1 hs.1 ht.2 hs.2))

/-- For a positive offer value, all candidate-specific continuation equalities
occur in a countable set of times, derived from the actual scalar values. -/
lemma FiniteIntensityHybridInstance.thresholdTime_eq_countable
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c x : ℝ} (hw : 0 < w) (hc : 0 < c) (hx : 0 < x)
    (A : Finset (Fin n)) (i : Option (Fin n)) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x = B.valueHybridThreshold w c () A t i}.Countable := by
  let C := B.restrictIndividuals (i.elim A (fun j => A.erase j))
  have hC : C.terminal = 0 := ha
  have hCount := (C.continuationTime_positive_level_subsingleton hC hw hc (mul_pos hw hx)).countable
  apply hCount.mono
  intro t ht
  refine ⟨ht.1,?_⟩
  have hEq := ht.2
  change x = C.continuationValue w c (remainingTime t)/w at hEq
  have hMul := (eq_div_iff hw.ne').mp hEq
  nlinarith

/-- Every fixed mark has null threshold-equality times. Zero and negative
marks are handled by the positive preterminal waiting value. -/
theorem FiniteIntensityHybridInstance.thresholdTime_ne_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (x : ℝ) :
    ∀ᵐ t ∂Model.Instance.uniformClock, ∀ A i, x ≠ B.valueHybridThreshold w c () A t i := by
  by_cases hx : 0 < x
  · apply ae_all_iff.mpr
    intro A
    apply ae_all_iff.mpr
    intro i
    have hNull := (B.thresholdTime_eq_countable ha hw hc hx A i).measure_zero Model.Instance.uniformClock
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNull,uniformClock_mem_Ioo] with t ht hTime
    intro hEq
    exact ht ⟨⟨hTime.1.le,hTime.2.le⟩,hEq⟩
  · filter_upwards [uniformClock_mem_Ioo] with t ht
    intro A i hEq
    have hPos := B.valueHybridThreshold_pos hw hc A i ht.2
    rw [← hEq] at hPos
    exact (not_lt.mp hx).not_gt hPos

end ProphetSecretary.Limiting
