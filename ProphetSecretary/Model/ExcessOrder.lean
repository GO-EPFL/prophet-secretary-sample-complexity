import ProphetSecretary.Model.ExcessValueMap

/-!
# Order properties of the excess map

The continuous totalization is monotone when the reserve is nonnegative. This
lets causal zero simulations transfer excess rewards using their proved reward
comparison, while retaining the original observation histories.
-/

namespace ProphetSecretary.Model

lemma excessValueMap_le_self {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : excessValueMap a x ≤ x := by
  unfold excessValueMap
  exact sub_le_self x (le_min ha (le_max_right _ _))

lemma excessValueMap_eq_self_of_nonpositive {a x : ℝ} (ha : 0 ≤ a) (hx : x ≤ 0) : excessValueMap a x = x := by
  unfold excessValueMap
  rw [max_eq_right hx,min_eq_right ha,sub_zero]

lemma excessValueMap_monotone {a : ℝ} (ha : 0 ≤ a) : Monotone (excessValueMap a) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · have hy := hx.trans hxy
    rw [excessValueMap_eq_positivePart hx,excessValueMap_eq_positivePart hy]
    exact max_le_max (sub_le_sub_right hxy a) le_rfl
  · have hxn : x ≤ 0 := (not_le.mp hx).le
    rw [excessValueMap_eq_self_of_nonpositive ha hxn]
    by_cases hy : 0 ≤ y
    · exact hxn.trans (excessValueMap_nonnegative hy)
    · rw [excessValueMap_eq_self_of_nonpositive ha (not_le.mp hy).le]
      exact hxy

end ProphetSecretary.Model
