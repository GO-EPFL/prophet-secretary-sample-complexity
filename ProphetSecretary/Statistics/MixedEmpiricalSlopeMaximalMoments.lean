import ProphetSecretary.Statistics.MixedEmpiricalSlopeBudgets

/-!
# Maximal moments of the mixed scalar-increment martingale

Second and sixth martingale maximal inequalities apply to the constructed
mixed process and its actual predictable budgets. Their constants are uniform
in both the number of identities and the set of exact known marginals.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedSlopeReverseMaximum (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  ProphetSecretary.Probability.runningMaximum (fun m => |mixedSlopeReverseProcess P known p z z' u m a|) (n * k)

lemma mixedSlopeReverseMaximum_nonnegative (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    0 ≤ mixedSlopeReverseMaximum P known p z z' u a :=
  ProphetSecretary.Probability.runningMaximum_nonnegative (fun _ => abs_nonneg _) _

lemma mixedSlopeReverseMaximum_integrable_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (r : ℕ) :
    Integrable (fun a => mixedSlopeReverseMaximum P known p z z' u a ^ r) (P.trainingCoordinateLaw k) := by
  have hS := mixedSlopeReverseProcess_martingale (k := k) P known hbound p hz (hz.trans hzz.le) u horder
  exact ProphetSecretary.Probability.integrable_runningMaximum_pow
    (ProphetSecretary.Probability.martingale_abs_submartingale hS).stronglyAdapted (fun _ _ => abs_nonneg _)
    (by exact div_nonneg (by positivity) (sub_nonneg.mpr hzz.le) : 0 ≤ 2 * ((n * k : ℕ) * (k : ℝ)⁻¹) / (z' - z))
    (fun m => mixedSlopeReverseProcess_bounded P known hbound p hz hzz u m) r (n * k)

/-- Fixed-clock second maximal moment of the normalized scalar increment. -/
theorem mixedSlopeReverseMaximum_secondMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, mixedSlopeReverseMaximum P known p z z' u a ^ 2 ∂P.trainingCoordinateLaw k) ≤
      (4 / (k : ℝ)) * (∫ a, mixedTrueSlopePremiumSum P known z z' u a
        ∂P.trainingCoordinateLaw k) := by
  have hS := mixedSlopeReverseProcess_martingale (k := k) P known hbound p hz (hz.trans hzz.le) u horder
  have hC : 0 ≤ 2 * ((n * k : ℕ) * (k : ℝ)⁻¹) / (z' - z) := div_nonneg (by positivity) (sub_nonneg.mpr hzz.le)
  have hB := fun m => mixedSlopeReverseProcess_bounded (k := k) P known hbound p hz hzz u m
  have hzero (a : (Fin n × Fin k) → ℝ) : mixedSlopeReverseProcess P known p z z' u 0 a = 0 := by
    simpa only [Pi.zero_apply] using congrFun (mixedSlopeReverseProcess_zero P known p z z' u) a
  have hmax := ProphetSecretary.Probability.martingale_runningAbsMaximum_square_le_variation hS hC hB hzero (n * k)
  have hQI : Integrable (ProphetSecretary.Probability.predictableQuadraticVariation (reverseTrainingFiltration p)
      (P.trainingCoordinateLaw k) (mixedSlopeReverseProcess P known p z z' u) (n * k)) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using ProphetSecretary.Probability.integrable_predictableQuadraticVariation_pow hC hB 1 (n * k)
  have hUI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      mixedTrueSlopePremiumSum P known z z' u a) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using integrable_mixedTrueSlopePremiumSum_fixed_pow P known (P.integrable_maximum_of_bounded hbound) hz hzz u hu 1
  have hEQ := integral_mono_ae hQI (hUI.div_const (k : ℝ))
    (mixedSlopeReverseProcess_quadraticVariation_le P known hbound p hz hzz u hu horder)
  rw [integral_div] at hEQ
  apply hmax.trans
  apply (mul_le_mul_of_nonneg_left hEQ (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  ring

/-- The actual sixth maximal moment uses the true premium third moment and first
moment, with one explicit universal constant and no instance-size factor. -/
theorem mixedSlopeReverseMaximum_sixthMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, mixedSlopeReverseMaximum P known p z z' u a ^ 6 ∂P.trainingCoordinateLaw k) ≤
      2000000000 * ((∫ a, mixedTrueSlopePremiumSum P known z z' u a ^ 3
        ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3 +
        (∫ a, mixedTrueSlopePremiumSum P known z z' u a
          ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5) := by
  have hS := mixedSlopeReverseProcess_martingale (k := k) P known hbound p hz (hz.trans hzz.le) u horder
  have hC : 0 ≤ 2 * ((n * k : ℕ) * (k : ℝ)⁻¹) / (z' - z) := div_nonneg (by positivity) (sub_nonneg.mpr hzz.le)
  have hB := fun m => mixedSlopeReverseProcess_bounded (k := k) P known hbound p hz hzz u m
  have hzero (a : (Fin n × Fin k) → ℝ) : mixedSlopeReverseProcess P known p z z' u 0 a = 0 := by
    simpa only [Pi.zero_apply] using congrFun (mixedSlopeReverseProcess_zero P known p z z' u) a
  have hmax := ProphetSecretary.Probability.martingale_runningAbsMaximum_sixth_le_variation hS hC hB hzero (n * k)
  have hQI3 := ProphetSecretary.Probability.integrable_predictableQuadraticVariation_pow
    (ℱ := reverseTrainingFiltration (k := k) p) hC hB 3 (n * k)
  have hUI3 := integrable_mixedTrueSlopePremiumSum_fixed_pow (k := k) P known (P.integrable_maximum_of_bounded hbound) hz hzz u hu 3
  have hright : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (mixedTrueSlopePremiumSum P known z z' u a / k) ^ 3)
      (P.trainingCoordinateLaw k) := by
    simpa only [div_pow] using hUI3.div_const ((k : ℝ) ^ 3)
  have hEQ3 := integral_mono_ae hQI3 hright (by
    filter_upwards [ProphetSecretary.Probability.predictableQuadraticVariation_bounds
      (ℱ := reverseTrainingFiltration (k := k) p) hC hB (n * k),
      mixedSlopeReverseProcess_quadraticVariation_le (k := k) P known hbound p hz hzz u hu horder] with a h0 h1
    exact pow_le_pow_left₀ h0.1 h1 3)
  simp only [div_pow] at hEQ3
  rw [integral_div] at hEQ3
  apply hmax.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add hEQ3 (mixedSlopeReverseProcess_sixth_jump_budget P known hbound p hz hzz u hu horder)) (by norm_num)

end ProphetSecretary.Model
