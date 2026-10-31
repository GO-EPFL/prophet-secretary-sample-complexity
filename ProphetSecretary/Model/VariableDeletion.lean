import ProphetSecretary.Model.StopLossStability

/-!
# The scalar cost of deleting one offer

Replacing a nonnegative marginal by a deterministic zero changes the actual
optimal scalar value by at most w times its first moment. Other marginal laws
and all identity observations remain present in this comparison. Erasing the
zero identity itself uses the separate causal zero-simulation theorem.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

lemma stopLoss_zero_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (h0 : ∀ᵐ x ∂μ, 0 ≤ x) (b : ℝ) : stopLoss (Measure.dirac (0 : ℝ)) b ≤ stopLoss μ b := by
  have h := integral_mono_ae (integrable_const (max 0 (-b))) (integrable_stopLoss μ hμ b)
    (h0.mono fun x hx => max_le_max le_rfl (by linarith : -b ≤ x - b))
  simpa only [stopLoss, integral_dirac, zero_sub, integral_const, probReal_univ, one_smul] using h

lemma stopLoss_le_zero_add_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (h0 : ∀ᵐ x ∂μ, 0 ≤ x) (b : ℝ) :
    stopLoss μ b ≤ stopLoss (Measure.dirac (0 : ℝ)) b + ∫ x, x ∂μ := by
  have hprem : Integrable (fun x => max 0 (x - b)) μ := integrable_stopLoss μ hμ b
  have hpoint : ∀ᵐ x ∂μ, max 0 (x - b) ≤ x + max 0 (-b) := h0.mono fun x hx => by
    apply max_le
    · linarith only [hx, le_max_left (0 : ℝ) (-b)]
    · linarith only [le_max_right (0 : ℝ) (-b)]
  have h := integral_mono_ae hprem (hμ.add (integrable_const (max 0 (-b)))) hpoint
  change (∫ x, max 0 (x - b) ∂μ) ≤ ∫ x, x + max 0 (-b) ∂μ at h
  rw [integral_add (μ := μ) (f := fun x : ℝ => x) (g := fun _ => max 0 (-b))
    hμ (integrable_const (max 0 (-b)))] at h
  simpa only [stopLoss, integral_dirac, zero_sub, integral_const, probReal_univ, one_smul, add_comm] using h

/-- Explicit one-variable scalar deletion bound, uniform in the instance size. -/
theorem Instance.optimalScalarValue_single_zero_loss {n : ℕ} (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (i : Fin n) (hzero : Q.law i = Measure.dirac (0 : ℝ))
    (hsame : ∀ j, j ≠ i → Q.law j = P.law j) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    0 ≤ optimalScalarValue P w c - optimalScalarValue Q w c ∧
      optimalScalarValue P w c - optimalScalarValue Q w c ≤ w * ∫ x, x ∂P.law i := by
  let d : Fin n → ℝ := fun j => if j = i then ∫ x, x ∂P.law i else 0
  have hmean : 0 ≤ ∫ x, x ∂P.law i := integral_nonneg_of_ae (P.nonnegative i)
  have hd : ∀ j, 0 ≤ d j := by intro j; dsimp [d]; split_ifs <;> positivity
  have herror : ∀ j b, stopLoss (P.law j) b ≤ stopLoss (Q.law j) b + d j := by
    intro j b
    by_cases hj : j = i
    · subst j
      simpa only [d, if_pos rfl, hzero] using
        stopLoss_le_zero_add_mean (P.law i) ((P.integrable_maximum_iff.mp hP) i) (P.nonnegative i) b
    · rw [hsame j hj]
      simp only [d, if_neg hj, add_zero, le_refl]
  have hQP : Q.StopLossLE P := by
    intro j b
    by_cases hj : j = i
    · subst j
      rw [hzero]
      exact stopLoss_zero_le (P.law i) ((P.integrable_maximum_iff.mp hP) i) (P.nonnegative i) b
    · rw [hsame j hj]
  have hsum : (∑ j, d j) = ∫ x, x ∂P.law i := by simp [d]
  have hupper := P.optimalScalarValue_le_of_stopLoss_error Q hP hQ d hd herror hw hc
  rw [hsum] at hupper
  have hlower := Q.optimalScalarValue_mono_stopLoss P hQ hP hQP hw hc
  exact ⟨sub_nonneg.mpr hlower, by linarith only [hupper]⟩

lemma Instance.marginalMean_le_cap_positiveProbability {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {H : ℝ}
    (hbound : ∀ᵐ x ∂P.law i, x ≤ H) :
    (∫ x, x ∂P.law i) ≤ H * (P.law i).real (Ioi 0) := by
  have hi : Integrable ((Ioi (0 : ℝ)).indicator (fun _ => H)) (P.law i) :=
    (integrable_const H : Integrable (fun _ : ℝ => H) (P.law i)).indicator measurableSet_Ioi
  have hId : Integrable (fun x : ℝ => x) (P.law i) := (P.integrable_maximum_iff.mp hP) i
  have h : (∫ x : ℝ, x ∂P.law i) ≤ ∫ x : ℝ, (Ioi (0 : ℝ)).indicator (fun _ => H) x ∂P.law i :=
    integral_mono_ae hId hi (by
    filter_upwards [hbound] with x hxH
    change x ≤ (Ioi (0 : ℝ)).indicator (fun _ => H) x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
      exact hxH
    · rw [Set.indicator_of_notMem hx]
      exact not_lt.mp hx)
  have heq := integral_indicator_const H (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi) (μ := P.law i)
  rw [heq] at h
  simpa only [smul_eq_mul, mul_comm] using h

end ProphetSecretary.Model
