import ProphetSecretary.Limiting.ReserveCutoffs
import ProphetSecretary.Probability.CenteredValueScore
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A continuous weight for ordering offers above a terminal reserve

A summable positive combination of continuous band ramps replaces the
indicator score in the compact-extraction proof. Its aggregate expectation is
bounded by one whenever the corresponding aggregate tail bounds hold. It
vanishes below the reserve and is strictly positive above it; hence division
by this weight recovers every band strictly above the reserve.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal BigOperators Classical
namespace ProphetSecretary.Limiting

noncomputable def reserveBandRamp (b : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (max 0 (x-b)) 1)
    ((continuous_const.max (continuous_id.sub continuous_const)).min continuous_const) 1
    (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (le_min (le_max_left _ _) zero_le_one)]; exact min_le_right _ _)

lemma reserveBandRamp_mem (b x : ℝ) : reserveBandRamp b x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_left _ _) zero_le_one,min_le_right _ _⟩
lemma reserveBandRamp_norm (b : ℝ) : ‖reserveBandRamp b‖ ≤ 1 :=
  (norm_le (by norm_num)).mpr fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (reserveBandRamp_mem b x).1]
    exact (reserveBandRamp_mem b x).2
lemma reserveBandRamp_zero {b x : ℝ} (hx : x ≤ b) : reserveBandRamp b x = 0 := by
  change min (max 0 (x-b)) 1 = 0
  rw [max_eq_left (sub_nonpos.mpr hx)]
  norm_num
lemma reserveBandRamp_pos {b x : ℝ} (hx : b < x) : 0 < reserveBandRamp b x := by
  change 0 < min (max 0 (x-b)) 1
  exact lt_min (lt_max_of_lt_right (sub_pos.mpr hx)) zero_lt_one
lemma reserveBandRamp_monotone (b : ℝ) : Monotone (reserveBandRamp b) := by
  intro x y hxy
  exact min_le_min (max_le_max le_rfl (sub_le_sub_right hxy b)) le_rfl

noncomputable def reserveWeightCoefficient (B : ℕ → ℝ≥0) (k : ℕ) : ℝ := (1/2 : ℝ)^(k+1) / B k
noncomputable def reserveWeightTerm (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (k : ℕ) : ℝ →ᵇ ℝ :=
  reserveWeightCoefficient B k • reserveBandRamp (b k)
noncomputable def reserveOrderingWeight (b : ℕ → ℝ) (B : ℕ → ℝ≥0) : ℝ →ᵇ ℝ :=
  ∑' k, reserveWeightTerm b B k

lemma reserveWeightCoefficient_nonneg (B : ℕ → ℝ≥0) (k : ℕ) : 0 ≤ reserveWeightCoefficient B k := by
  unfold reserveWeightCoefficient
  positivity
lemma reserveWeightCoefficient_pos (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) (k : ℕ) :
    0 < reserveWeightCoefficient B k := by
  apply div_pos (by positivity)
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hB k)
lemma reserveWeightCoefficient_le (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) (k : ℕ) :
    reserveWeightCoefficient B k ≤ (1/2 : ℝ)^(k+1) := by
  exact div_le_self (by positivity) (hB k)

lemma summable_reserve_geometric : Summable (fun k : ℕ => (1/2 : ℝ)^(k+1)) :=
  by
    simpa only [pow_succ'] using
      ((hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left (1/2 : ℝ)).summable
lemma tsum_reserve_geometric : (∑' k : ℕ, (1/2 : ℝ)^(k+1)) = 1 := by
  have h := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)
  have ht := h.mul_left (1/2 : ℝ)
  calc
    _ = ∑' k : ℕ, (1/2 : ℝ) * (1/2)^k := by simp only [pow_succ']
    _ = (1/2 : ℝ) * (1-(1/2 : ℝ))⁻¹ := ht.tsum_eq
    _ = 1 := by norm_num

lemma summable_reserveWeightTerm (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) :
    Summable (reserveWeightTerm b B) := by
  apply summable_reserve_geometric.of_norm_bounded
  intro k
  rw [reserveWeightTerm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (reserveWeightCoefficient_nonneg B k)]
  exact (mul_le_of_le_one_right (reserveWeightCoefficient_nonneg B k) (reserveBandRamp_norm (b k))).trans
    (reserveWeightCoefficient_le B hB k)

lemma reserveOrderingWeight_apply (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) (x : ℝ) :
    reserveOrderingWeight b B x = ∑' k, reserveWeightCoefficient B k * reserveBandRamp (b k) x := by
  exact (BoundedContinuousFunction.evalCLM ℝ x).map_tsum (summable_reserveWeightTerm b B hB)

lemma summable_reserveWeight_apply (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) (x : ℝ) :
    Summable (fun k => reserveWeightCoefficient B k * reserveBandRamp (b k) x) :=
  ((BoundedContinuousFunction.evalCLM ℝ x).hasSum (summable_reserveWeightTerm b B hB).hasSum).summable

lemma reserveOrderingWeight_nonneg (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) (x : ℝ) :
    0 ≤ reserveOrderingWeight b B x := by
  rw [reserveOrderingWeight_apply b B hB]
  exact tsum_nonneg fun k => mul_nonneg (reserveWeightCoefficient_nonneg B k) (reserveBandRamp_mem _ _).1

lemma reserveOrderingWeight_monotone (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k) :
    Monotone (reserveOrderingWeight b B) := by
  intro x y hxy
  rw [reserveOrderingWeight_apply b B hB,reserveOrderingWeight_apply b B hB]
  exact (summable_reserveWeight_apply b B hB x).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (reserveBandRamp_monotone (b k) hxy)
      (reserveWeightCoefficient_nonneg B k)) (summable_reserveWeight_apply b B hB y)

lemma reserveOrderingWeight_zero {a : ℝ} (b : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hB : ∀ k, 1 ≤ B k) (hb : ∀ k, a < b k) {x : ℝ} (hx : x ≤ a) :
    reserveOrderingWeight b B x = 0 := by
  rw [reserveOrderingWeight_apply b B hB]
  have heq (k : ℕ) : reserveWeightCoefficient B k * reserveBandRamp (b k) x = 0 := by
    rw [reserveBandRamp_zero (hx.trans (hb k).le),mul_zero]
  simp_rw [heq]
  exact tsum_zero

lemma reserveOrderingWeight_pos {a x : ℝ} (b : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hB : ∀ k, 1 ≤ B k) (hlim : Tendsto b atTop (𝓝 a)) (hx : a < x) :
    0 < reserveOrderingWeight b B x := by
  obtain ⟨k,hk⟩ := ((tendsto_order.mp hlim).2 x hx).exists
  rw [reserveOrderingWeight_apply b B hB]
  exact (mul_pos (reserveWeightCoefficient_pos B hB k) (reserveBandRamp_pos hk)).trans_le
    (Summable.le_tsum (summable_reserveWeight_apply b B hB x) k
      (fun j _ => mul_nonneg (reserveWeightCoefficient_nonneg B j) (reserveBandRamp_mem _ _).1))

end ProphetSecretary.Limiting
