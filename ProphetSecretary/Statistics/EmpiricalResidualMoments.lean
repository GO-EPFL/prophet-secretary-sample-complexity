import ProphetSecretary.Statistics.EmpiricalResidual
import ProphetSecretary.Statistics.EmpiricalMoments

/-!
# Localized moments of actual empirical Bellman residuals

The empirical continuation is first shown independent of the candidate's complete
training row. Its residual is then a centered sample average under the true candidate
law. Constants depend on its true positive premium, not on the instance size.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- Fixed candidate-row residual moments; the scalar is held fixed throughout the
candidate-row integral. This does not claim unbiasedness for a data-selected scalar. -/
theorem Instance.empirical_transitionResidual_row_moments (P : Instance n)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ 1) (y : Reservoir n k) (i : Fin n)
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) :
    let θ := (totalEmpiricalInstance y).continuationAtArrival 1 z (fun _ => 0) u i
    let p := positivePremium (P.law i) 1 θ
    (∫ v : Fin k → ℝ,
      ((totalEmpiricalInstance (Function.update y i v)).transitionResidual P 1 z u i) ^ 2
      ∂Measure.pi (fun _ : Fin k => P.law i)) ≤ p / k ∧
    (∫ v : Fin k → ℝ,
      ((totalEmpiricalInstance (Function.update y i v)).transitionResidual P 1 z u i) ^ 4
      ∂Measure.pi (fun _ : Fin k => P.law i)) ≤ p / (k : ℝ) ^ 3 + 3 * p ^ 2 / (k : ℝ) ^ 2 := by
  let θ := (totalEmpiricalInstance y).continuationAtArrival 1 z (fun _ => 0) u i
  let p := positivePremium (P.law i) 1 θ
  let f : ℝ → ℝ := fun x => max (max 0 x - θ) 0
  have hθ : 0 ≤ θ := (totalEmpiricalInstance y).continuationAtArrival_nonnegative
    (totalEmpiricalInstance_integrable y) zero_le_one hz _ u i
  have hfm : Measurable f := ((measurable_const.max measurable_id).sub measurable_const).max measurable_const
  have hb : ∀ᵐ x ∂P.law i, 0 ≤ f x ∧ f x ≤ 1 := by
    filter_upwards [P.nonnegative i, hbound i] with x hx0 hx1
    dsimp [f]
    rw [max_eq_right hx0]
    exact ⟨le_max_right _ _, max_le (by linarith) zero_le_one⟩
  have hmean : (∫ x, f x ∂P.law i) = p := by
    apply integral_congr_ae
    filter_upwards [P.nonnegative i] with x hx
    simp only [f, max_eq_right hx, one_mul]
  have hmom := ProphetSecretary.Statistics.empirical_average_centered_moment_bounds (k := k) hfm hb
  dsimp only at hmom
  rw [hmean] at hmom
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  have heq (v : Fin k → ℝ) :
      (totalEmpiricalInstance (Function.update y i v)).transitionResidual P 1 z u i =
        (k : ℝ)⁻¹ * ∑ j, (f (v j) - p) := by
    rw [totalEmpiricalInstance_transitionResidual_update_row]
    simp only [one_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    change (k : ℝ)⁻¹ * (∑ j, f (v j)) - p = (k : ℝ)⁻¹ * ((∑ j, f (v j)) - (k : ℝ) * p)
    field_simp
  constructor
  · calc
      _ = ∫ v : Fin k → ℝ, ((k : ℝ)⁻¹ * ∑ j, (f (v j) - p)) ^ 2
          ∂Measure.pi (fun _ : Fin k => P.law i) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun v => congrArg (fun a : ℝ => a ^ 2) (heq v))
      _ ≤ p / k := hmom.1
  · calc
      _ = ∫ v : Fin k → ℝ, ((k : ℝ)⁻¹ * ∑ j, (f (v j) - p)) ^ 4
          ∂Measure.pi (fun _ : Fin k => P.law i) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun v => congrArg (fun a : ℝ => a ^ 4) (heq v))
      _ ≤ p / (k : ℝ) ^ 3 + 3 * p ^ 2 / (k : ℝ) ^ 2 := hmom.2

/-- One sample-by-sample reverse residual jump. The full online vector and future
training rows are analytical parameters, not extra observations supplied to the policy. -/
noncomputable def Instance.empiricalPremiumJump (P : Instance n) (k : ℕ)
    (i : Fin n) (θ x : ℝ) : ℝ :=
  (k : ℝ)⁻¹ * (max (max 0 x - θ) 0 - positivePremium (P.law i) 1 θ)

lemma Instance.transitionResidual_update_row_eq_sum_jumps (P : Instance n)
    (y : Reservoir n k) (i : Fin n) (v : Fin k → ℝ) (z : ℝ) (u : Fin n → ℝ) :
    (totalEmpiricalInstance (Function.update y i v)).transitionResidual P 1 z u i =
      ∑ j : Fin k, P.empiricalPremiumJump k i
        ((totalEmpiricalInstance y).continuationAtArrival 1 z (fun _ => 0) u i) (v j) := by
  rw [totalEmpiricalInstance_transitionResidual_update_row]
  simp only [Instance.empiricalPremiumJump, one_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  field_simp

omit [NeZero k] in
/-- Explicit conditional jump bounds used in the predictable quadratic variation
and sixth-jump sum. The threshold is fixed during the fresh-sample integral. -/
theorem Instance.empiricalPremiumJump_moments (P : Instance n) (i : Fin n)
    (hbound : ∀ᵐ x ∂P.law i, x ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    let p := positivePremium (P.law i) 1 θ
    (∫ x, P.empiricalPremiumJump k i θ x ∂P.law i) = 0 ∧
    (∫ x, (P.empiricalPremiumJump k i θ x) ^ 2 ∂P.law i) ≤ p / (k : ℝ) ^ 2 ∧
    (∫ x, (P.empiricalPremiumJump k i θ x) ^ 6 ∂P.law i) ≤ p / (k : ℝ) ^ 6 := by
  let p := positivePremium (P.law i) 1 θ
  let f : ℝ → ℝ := fun x => max (max 0 x - θ) 0
  have hfm : Measurable f := ((measurable_const.max measurable_id).sub measurable_const).max measurable_const
  have hb : ∀ᵐ x ∂P.law i, 0 ≤ f x ∧ f x ≤ 1 := by
    filter_upwards [P.nonnegative i, hbound] with x hx0 hx1
    dsimp [f]
    rw [max_eq_right hx0]
    exact ⟨le_max_right _ _, max_le (by linarith) zero_le_one⟩
  have hmean : (∫ x, f x ∂P.law i) = p := by
    apply integral_congr_ae
    filter_upwards [P.nonnegative i] with x hx
    simp only [f, max_eq_right hx, one_mul]
  obtain ⟨_hp0, _hp1, _habs, hcenter, h2, _h4⟩ := ProphetSecretary.Statistics.bounded_centered_moments hfm hb
  have h6 := ProphetSecretary.Statistics.bounded_centered_sixthMoment_le_mean hfm hb
  rw [hmean] at hcenter h2 h6
  have he (a : ℕ) : (∫ x, (P.empiricalPremiumJump k i θ x) ^ a ∂P.law i) =
      ((k : ℝ)⁻¹) ^ a * ∫ x, (f x - p) ^ a ∂P.law i := by
    change (∫ x, ((k : ℝ)⁻¹ * (f x - p)) ^ a ∂P.law i) = _
    simp only [mul_pow]
    exact integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · change (∫ x, (k : ℝ)⁻¹ * (f x - p) ∂P.law i) = 0
    rw [integral_const_mul, hcenter, mul_zero]
  · rw [he 2]
    apply (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)).trans_eq
    simp only [div_eq_mul_inv, inv_pow]
    ring
  · rw [he 6]
    apply (mul_le_mul_of_nonneg_left h6 (by positivity)).trans_eq
    simp only [div_eq_mul_inv, inv_pow]
    ring

end ProphetSecretary.Model
