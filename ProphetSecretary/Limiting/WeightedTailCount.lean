import ProphetSecretary.Limiting.WeightedOrderedTails
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Uniform finite tail-count control from the extracted ordering weight
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped BigOperators

namespace ProphetSecretary.Limiting

lemma tailCount_le_inverse_weight {n : ℕ} (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgt : Monotone wgt)
    (hWeight : (∑ i, ∫ x, wgt x ∂P.law i) ≤ 1) {b : ℝ} (hb : 0 < wgt b) :
    P.tailCount b ≤ 1/wgt b := by
  apply (le_div_iff₀ hb).mpr
  have hSum : (∑ i, wgt b*(P.law i).real (Ioi b)) ≤ ∑ i, ∫ x, wgt x ∂P.law i := by
    apply Finset.sum_le_sum
    intro i _
    exact tail_mass_mul_le_integral_weight (P.marginalProbabilityLaw i) wgt hwgt0
      (fun _ hx => hwgt hx.le)
  change P.tailCount b*wgt b ≤ 1
  calc
    _ = ∑ i, wgt b*(P.law i).real (Ioi b) := by
      unfold Model.Instance.tailCount
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ ≤ _ := hSum.trans hWeight

end ProphetSecretary.Limiting
