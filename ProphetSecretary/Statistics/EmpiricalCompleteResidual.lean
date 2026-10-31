import ProphetSecretary.Statistics.EmpiricalReverseProcess

/-!
# Complete and individual empirical residual sums

The complete reverse process equals the full arrival residual sum. Each individual
marginal residual is the sum of its `k` fresh sample jumps. At a fixed scalar, all
individual training means therefore vanish. Deterministic clock-conditional reach
weights may multiply these identities; training-selected weights are not substituted.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma empiricalReverseJump_at_coordinate (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (q : Fin n × Fin k) :
    empiricalReverseJump P p z u ((reverseSampleOrder p).symm q).val =
      (fun a => P.empiricalPremiumJump k q.1 (empiricalArrivalContinuation 1 z u q.1 a) (a q)) := by
  let m : Fin (n * k) := (reverseSampleOrder p).symm q
  have he : reverseSampleOrder p ⟨m.val, m.is_lt⟩ = q := by
    change reverseSampleOrder p ((reverseSampleOrder p).symm q) = q
    exact (reverseSampleOrder p).apply_symm_apply q
  funext a
  change empiricalReverseJump P p z u m.val a = _
  rw [empiricalReverseJump, dif_pos m.is_lt, he]

/-- The terminal sample sum is precisely the complete offer-vector residual sum. -/
lemma empiricalReverseProcess_terminal_eq_residual_sum (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    empiricalReverseProcess P p z u (n * k) a =
      ∑ i : Fin n, (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i := by
  let y := reservoirCoordinates.symm a
  let f : Fin n × Fin k → ℝ := fun q => P.empiricalPremiumJump k q.1
    (empiricalArrivalContinuation 1 z u q.1 a) (a q)
  have hfin (m : Fin (n * k)) : empiricalReverseJump P p z u m.val a = f (reverseSampleOrder p m) := by
    simp only [empiricalReverseJump, dif_pos m.is_lt]
    rfl
  calc
    _ = ∑ m ∈ Finset.range (n * k), empiricalReverseJump P p z u m a := by
      simp only [empiricalReverseProcess, Nat.min_self, Finset.sum_apply]
    _ = ∑ m : Fin (n * k), empiricalReverseJump P p z u m.val a :=
      (Fin.sum_univ_eq_sum_range (fun m => empiricalReverseJump P p z u m a) (n * k)).symm
    _ = ∑ m : Fin (n * k), f (reverseSampleOrder p m) := Finset.sum_congr rfl (fun m _ => hfin m)
    _ = ∑ q : Fin n × Fin k, f q := (reverseSampleOrder p).sum_comp f
    _ = ∑ i : Fin n, ∑ j : Fin k, f (i, j) := Fintype.sum_prod_type f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have h := P.transitionResidual_update_row_eq_sum_jumps y i (y i) z u
      rw [Function.update_eq_self] at h
      exact h.symm

lemma empiricalReverseJump_integrable (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    Integrable (empiricalReverseJump (k := k) P p z u m) (P.trainingCoordinateLaw k) := by
  have hS := empiricalReverseProcess_martingale (k := k) P hbound p hz u horder
  rw [← empiricalReverseProcess_increment]
  exact (hS.integrable (m + 1)).sub (hS.integrable m)

lemma empiricalReverseJump_integral_zero (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    (∫ a, empiricalReverseJump (k := k) P p z u m a ∂P.trainingCoordinateLaw k) = 0 := by
  calc
    _ = ∫ a, ((P.trainingCoordinateLaw k)[empiricalReverseJump P p z u m | reverseTrainingFiltration p m]) a
        ∂P.trainingCoordinateLaw k := (integral_condExp ((reverseTrainingFiltration (k := k) p).le m)).symm
    _ = 0 := integral_eq_zero_of_ae (empiricalReverseJump_condExp_zero P hbound p hz u horder m)

lemma empirical_transitionResidual_eq_sample_sum (P : Instance n) (z : ℝ) (u : Fin n → ℝ)
    (i : Fin n) (a : (Fin n × Fin k) → ℝ) :
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i =
      ∑ j : Fin k, P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z u i a) (a (i, j)) := by
  have h := P.transitionResidual_update_row_eq_sum_jumps (reservoirCoordinates.symm a) i
    ((reservoirCoordinates.symm a) i) z u
  rw [Function.update_eq_self] at h
  exact h

/-- An individual complete residual is integrable under the actual training law. -/
lemma integrable_empirical_transitionResidual (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (i : Fin n) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i) (P.trainingCoordinateLaw k) := by
  have hfun : (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i) =
      (fun a => ∑ j : Fin k, P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z u i a) (a (i, j))) :=
    funext (empirical_transitionResidual_eq_sample_sum P z u i)
  rw [hfun]
  apply integrable_finsetSum
  intro j _
  rw [← empiricalReverseJump_at_coordinate P p z u (i, j)]
  exact empiricalReverseJump_integrable P hbound p hz u horder _

/-- Fixed-scalar individual centering; the current row's exclusion is essential. -/
theorem integral_empirical_transitionResidual_zero (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (i : Fin n) :
    (∫ a : (Fin n × Fin k) → ℝ,
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i
      ∂P.trainingCoordinateLaw k) = 0 := by
  have hfun : (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i) =
      (fun a => ∑ j : Fin k, P.empiricalPremiumJump k i (empiricalArrivalContinuation 1 z u i a) (a (i, j))) :=
    funext (empirical_transitionResidual_eq_sample_sum P z u i)
  rw [hfun, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    rw [← empiricalReverseJump_at_coordinate P p z u (i, j)]
    exact empiricalReverseJump_integral_zero P hbound p hz u horder _
  · intro j _
    rw [← empiricalReverseJump_at_coordinate P p z u (i, j)]
    exact empiricalReverseJump_integrable P hbound p hz u horder _

/-- Clock-conditional reach weights of a training-independent policy may be fixed
here. A selector depending on training is not substituted into this identity. -/
theorem integral_weighted_empirical_transitionResidual_zero (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (r : Fin n → ℝ) :
    (∫ a : (Fin n × Fin k) → ℝ, ∑ i : Fin n,
      r i * (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i
      ∂P.trainingCoordinateLaw k) = 0 := by
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul, integral_empirical_transitionResidual_zero P hbound p hz u horder i, mul_zero]
  · intro i _
    exact (integrable_empirical_transitionResidual P hbound p hz u horder i).const_mul (r i)

end ProphetSecretary.Model
