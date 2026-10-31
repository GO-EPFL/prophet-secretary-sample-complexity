import ProphetSecretary.Statistics.MixedEmpiricalReverseBudgets

/-!
# Maximal moments for the mixed empirical reverse martingale

Actual independent-sample conditional moments and the constructed predictable
variation yield the second and sixth maximal estimates. Known marginals add no
jumps. All statistical constants remain independent of the number of identities.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedReverseMaximum (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  ProphetSecretary.Probability.runningMaximum (fun m => |mixedReverseProcess P known p z u m a|) (n * k)

lemma mixedReverseMaximum_nonnegative (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    0 ≤ mixedReverseMaximum P known p z u a :=
  ProphetSecretary.Probability.runningMaximum_nonnegative (fun _ => abs_nonneg _) _

lemma mixedReverseMaximum_integrable_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (r : ℕ) :
    Integrable (fun a => mixedReverseMaximum P known p z u a ^ r) (P.trainingCoordinateLaw k) := by
  have hS := mixedReverseProcess_martingale (k := k) P known hbound p hz u horder
  exact ProphetSecretary.Probability.integrable_runningMaximum_pow
    (ProphetSecretary.Probability.martingale_abs_submartingale hS).stronglyAdapted (fun _ _ => abs_nonneg _)
    (by positivity : 0 ≤ (n * k : ℕ) * (k : ℝ)⁻¹)
    (fun m => mixedReverseProcess_bounded P known hbound p hz u m) r (n * k)

/-- The actual fixed-clock second maximal moment has the paper's variance budget. -/
theorem mixedReverseMaximum_secondMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, mixedReverseMaximum P known p z u a ^ 2 ∂P.trainingCoordinateLaw k) ≤
      (4 / (k : ℝ)) * (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) := by
  have hS := mixedReverseProcess_martingale (k := k) P known hbound p hz u horder
  have hC : 0 ≤ (n * k : ℕ) * (k : ℝ)⁻¹ := by positivity
  have hB := fun m => mixedReverseProcess_bounded (k := k) P known hbound p hz u m
  have hzero (a : (Fin n × Fin k) → ℝ) : mixedReverseProcess P known p z u 0 a = 0 := by
    simpa only [Pi.zero_apply] using congrFun (mixedReverseProcess_zero P known p z u) a
  have hmax := ProphetSecretary.Probability.martingale_runningAbsMaximum_square_le_variation hS hC hB hzero (n * k)
  have hQI : Integrable (ProphetSecretary.Probability.predictableQuadraticVariation (reverseTrainingFiltration p)
      (P.trainingCoordinateLaw k) (mixedReverseProcess P known p z u) (n * k)) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using ProphetSecretary.Probability.integrable_predictableQuadraticVariation_pow hC hB 1 (n * k)
  have hUI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using integrable_mixedTruePremium_pow P known hbound hz u 1
  have hEQ := integral_mono_ae hQI (hUI.div_const (k : ℝ))
    (mixedReverseProcess_quadraticVariation_le P known hbound p hz u horder)
  rw [integral_div] at hEQ
  apply hmax.trans
  apply (mul_le_mul_of_nonneg_left hEQ (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  ring

/-- The actual sixth maximal moment uses the true premium third moment and first
moment, with one explicit universal constant and no instance-size factor. -/
theorem mixedReverseMaximum_sixthMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, mixedReverseMaximum P known p z u a ^ 6 ∂P.trainingCoordinateLaw k) ≤
      2000000000 * ((∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3
        ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3 +
        (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
          ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5) := by
  have hS := mixedReverseProcess_martingale (k := k) P known hbound p hz u horder
  have hC : 0 ≤ (n * k : ℕ) * (k : ℝ)⁻¹ := by positivity
  have hB := fun m => mixedReverseProcess_bounded (k := k) P known hbound p hz u m
  have hzero (a : (Fin n × Fin k) → ℝ) : mixedReverseProcess P known p z u 0 a = 0 := by
    simpa only [Pi.zero_apply] using congrFun (mixedReverseProcess_zero P known p z u) a
  have hmax := ProphetSecretary.Probability.martingale_runningAbsMaximum_sixth_le_variation hS hC hB hzero (n * k)
  have hQI3 := ProphetSecretary.Probability.integrable_predictableQuadraticVariation_pow
    (ℱ := reverseTrainingFiltration (k := k) p) hC hB 3 (n * k)
  have hUI3 := integrable_mixedTruePremium_pow (k := k) P known hbound hz u 3
  have hright : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / k) ^ 3)
      (P.trainingCoordinateLaw k) := by
    simpa only [div_pow] using hUI3.div_const ((k : ℝ) ^ 3)
  have hEQ3 := integral_mono_ae hQI3 hright (by
    filter_upwards [ProphetSecretary.Probability.predictableQuadraticVariation_bounds
      (ℱ := reverseTrainingFiltration (k := k) p) hC hB (n * k),
      mixedReverseProcess_quadraticVariation_le (k := k) P known hbound p hz u horder] with a h0 h1
    exact pow_le_pow_left₀ h0.1 h1 3)
  simp only [div_pow] at hEQ3
  rw [integral_div] at hEQ3
  apply hmax.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add hEQ3 (mixedReverseProcess_sixth_jump_budget P known hbound p hz u horder)) (by norm_num)

end ProphetSecretary.Model
