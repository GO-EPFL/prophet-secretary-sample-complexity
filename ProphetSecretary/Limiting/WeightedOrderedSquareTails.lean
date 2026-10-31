import ProphetSecretary.Limiting.WeightedOrderedTails

/-!
# Explicit square-sum error bounds after reserve-weight ordering

The first N retained coordinates leave an upper-band probability square sum
at most 1/[c²(N+1)], when the continuous ordering weight is at least c>0
on that band and its total expectation is at most one.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma sum_weightOrderedPadded_scores (P : Model.Instance n) (w : ℝ →ᵇ ℝ) :
    (∑ i : Fin n, ∫ x, w x ∂(weightOrderedPaddedLaw P w i.val : Measure ℝ)) =
      ∑ i, ∫ x, w x ∂P.law i := by
  calc
    _ = ∑ i : Fin n, ∫ x, w x ∂(weightOrderedMarginalLaw P w i : Measure ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightOrderedPaddedLaw_of_lt P w i.isLt]
    _ = _ := sum_weightOrdered_scores P w

lemma weightOrderedPaddedLaw_residual_tail_le (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0) (hWeight : (∑ i, ∫ x, w x ∂P.law i) ≤ 1)
    {b c : ℝ} (hc : 0 < c) (hband : ∀ x, b < x → c ≤ w x) {N j : ℕ} (hNj : N ≤ j) :
    (weightOrderedPaddedLaw P w j : Measure ℝ).real (Ioi b) ≤ 1 / (c * (N+1 : ℕ)) := by
  apply (weightOrderedPaddedLaw_tail_le P w hw hw0 hWeight hc hband j).trans
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < c * (N+1 : ℕ))
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.add_le_add_right hNj 1)) hc.le

theorem weightOrderedPaddedLaw_residual_tail_square_sum_le (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0) (hWeight : (∑ i, ∫ x, w x ∂P.law i) ≤ 1)
    {b c : ℝ} (hc : 0 < c) (hband : ∀ x, b < x → c ≤ w x) (N : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
      (weightOrderedPaddedLaw P w i.val : Measure ℝ).real (Ioi b)^2) ≤ 1 / (c^2 * (N+1 : ℕ)) := by
  let p : Fin n → ℝ := fun i => (weightOrderedPaddedLaw P w i.val : Measure ℝ).real (Ioi b)
  let A := Finset.univ.filter (fun i : Fin n => N ≤ i.val)
  let M := 1 / (c * (N+1 : ℕ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp (i : Fin n) : 0 ≤ p i := measureReal_nonneg
  have htotal : (∑ i : Fin n, p i) ≤ 1/c := by
    apply (le_div_iff₀ hc).mpr
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i : Fin n, ∫ x, w x ∂(weightOrderedPaddedLaw P w i.val : Measure ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [mul_comm] using tail_mass_mul_le_integral_weight (weightOrderedPaddedLaw P w i.val) w hw hband
      _ = ∑ i, ∫ x, w x ∂P.law i := sum_weightOrderedPadded_scores P w
      _ ≤ 1 := hWeight
  have hres : (∑ i ∈ A, p i) ≤ 1/c :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)).trans htotal
  calc
    (∑ i ∈ A, p i^2) ≤ ∑ i ∈ A, M*p i := by
      apply Finset.sum_le_sum
      intro i hi
      have hbnd : p i ≤ M := weightOrderedPaddedLaw_residual_tail_le P w hw hw0 hWeight hc hband (Finset.mem_filter.mp hi).2
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hbnd (hp i)
    _ = M * ∑ i ∈ A, p i := by rw [Finset.mul_sum]
    _ ≤ M * (1/c) := mul_le_mul_of_nonneg_left hres hM
    _ = _ := by dsimp [M]; field_simp

end ProphetSecretary.Limiting
