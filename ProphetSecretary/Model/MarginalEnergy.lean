import ProphetSecretary.Model.MarginalPremium
import Mathlib.Probability.Moments.Variance

/-!
# Energy of marginal acceptance premia

Reach-duration comparison and the fact that at most one offer is selected give
an explicit squared-norm bound. No identification with an envelope gradient is
assumed; that identification is established separately from the residual law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.marginalPremium_memLp_two (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) (i : Fin n) :
    MemLp (P.marginalPremium hP hw hc i) 2 (P.law i) := by
  apply MemLp.of_bound (P.measurable_marginalPremium hP hw hc i).aestronglyMeasurable (w * H)
  filter_upwards [hbound i] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg (P.marginalPremium_nonnegative hP hw hc i a)]
  exact (P.marginalPremium_le hP hw hc i a).trans
    (mul_le_mul_of_nonneg_left (max_le ha hH) hw.le)

/-- The sum of the uncentered second moments is bounded by the product of
actual canonical duration and reward, with no finite-cardinality factor. -/
theorem Instance.marginalPremium_secondMoment_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) :
    (∑ i : Fin n, ∫ a, (P.marginalPremium hP hw hc i a) ^ 2 ∂P.law i) ≤
      2 * w ^ 2 * H * (P.valuePolicy hP hw.le hc).expectedDuration P *
        (P.valuePolicy hP hw.le hc).expectedReward P := by
  let C := P.valuePolicy hP hw.le hc
  let B := 2 * w * H * C.expectedDuration P
  have hT := C.expectedDuration_nonnegative P
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hEach (i : Fin n) : (∫ a, (P.marginalPremium hP hw hc i a) ^ 2 ∂P.law i) ≤
      B * ∫ a, P.marginalPremium hP hw hc i a ∂P.law i := by
    have h := integral_mono_ae (P.marginalPremium_memLp_two hP hw hc hH hbound i).integrable_sq
      ((P.integrable_marginalPremium hP hw hc hH hbound i).const_mul B) (by
        filter_upwards [hbound i] with a ha
        have h0 := P.marginalPremium_nonnegative hP hw hc i a
        have h1 := P.marginalPremium_le_duration hP hw hc hH ha i
        change P.marginalPremium hP hw hc i a ≤ B at h1
        nlinarith)
    simpa only [integral_const_mul] using h
  calc
    _ ≤ ∑ i : Fin n, B * ∫ a, P.marginalPremium hP hw hc i a ∂P.law i :=
      Finset.sum_le_sum (fun i _ ↦ hEach i)
    _ = B * ∑ i : Fin n, ∫ a, P.marginalPremium hP hw hc i a ∂P.law i := (Finset.mul_sum _ _ _).symm
    _ ≤ B * (w * C.expectedReward P) :=
      mul_le_mul_of_nonneg_left (P.sum_integral_marginalPremium_le hP hw hc hH hbound) hB
    _ = _ := by dsimp [B]; ring

/-- Centering can only reduce the energy. The resulting variance sum is the
squared Fisher norm once marginal score coordinates are identified. -/
theorem Instance.marginalPremium_varianceSum_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) :
    (∑ i : Fin n, variance (P.marginalPremium hP hw hc i) (P.law i)) ≤
      2 * w ^ 2 * H * (P.valuePolicy hP hw.le hc).expectedDuration P *
        (P.valuePolicy hP hw.le hc).expectedReward P := by
  apply (Finset.sum_le_sum (fun i _ ↦ variance_le_expectation_sq
    (P.measurable_marginalPremium hP hw hc i).aestronglyMeasurable)).trans
    (P.marginalPremium_secondMoment_le hP hw hc hH hbound)

end ProphetSecretary.Model
