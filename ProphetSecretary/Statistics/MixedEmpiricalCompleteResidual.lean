import ProphetSecretary.Statistics.MixedEmpiricalReverseProcess
import ProphetSecretary.Statistics.MixedEmpiricalResidual

/-!
# Mixed residuals equal actual reverse sample sums

Every known marginal has zero residual and zero sample jumps. For every unknown
marginal, summing its k centered jumps gives precisely its Bellman residual.
The terminal reverse process therefore matches the complete residual sum.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.mixed_transitionResidual_update_row_eq_sum_jumps (P : Instance n)
    (known : Finset (Fin n)) (y : Reservoir n k) (i : Fin n) (v : Fin k → ℝ) (z : ℝ) (u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known (Function.update y i v)).transitionResidual P 1 z u i =
      ∑ l : Fin k, P.mixedPremiumJump known k i
        ((mixedEmpiricalInstance P known y).continuationAtArrival 1 z (fun _ => 0) u i) (v l) := by
  by_cases hi : i∈known
  · simp only [mixedEmpiricalInstance_transitionResidual_known_zero P known _ hi,
      Instance.mixedPremiumJump,if_pos hi,Finset.sum_const_zero]
  · rw [mixedEmpiricalInstance_transitionResidual_update_unknown_row P known y hi]
    simp only [Instance.mixedPremiumJump,if_neg hi,Instance.empiricalPremiumJump,one_mul,←Finset.mul_sum,
      Finset.sum_sub_distrib,Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
    have hk : (k:ℝ)≠0 := by exact_mod_cast (NeZero.ne k)
    field_simp

lemma mixed_transitionResidual_eq_sample_sum (P : Instance n) (known : Finset (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (i : Fin n) (a : (Fin n × Fin k) → ℝ) :
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i =
      ∑ l : Fin k, P.mixedPremiumJump known k i
        (mixedArrivalContinuation P known 1 z u i a) (a (i,l)) := by
  have h := P.mixed_transitionResidual_update_row_eq_sum_jumps known (reservoirCoordinates.symm a) i
    ((reservoirCoordinates.symm a) i) z u
  rw [Function.update_eq_self] at h
  exact h

lemma mixedReverseJump_at_coordinate (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (q : Fin n × Fin k) :
    mixedReverseJump P known p z u ((reverseSampleOrder p).symm q).val =
      (fun a => P.mixedPremiumJump known k q.1 (mixedArrivalContinuation P known 1 z u q.1 a) (a q)) := by
  let m : Fin (n * k) := (reverseSampleOrder p).symm q
  have he : reverseSampleOrder p ⟨m.val, m.is_lt⟩ = q := by
    change reverseSampleOrder p ((reverseSampleOrder p).symm q) = q
    exact (reverseSampleOrder p).apply_symm_apply q
  funext a
  change mixedReverseJump P known p z u m.val a = _
  rw [mixedReverseJump, dif_pos m.is_lt, he]

/-- The terminal sample sum is precisely the complete offer-vector residual sum. -/
lemma mixedReverseProcess_terminal_eq_residual_sum (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    mixedReverseProcess P known p z u (n * k) a =
      ∑ i : Fin n, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i := by
  let f : Fin n × Fin k → ℝ := fun q => P.mixedPremiumJump known k q.1
    (mixedArrivalContinuation P known 1 z u q.1 a) (a q)
  have hfin (m : Fin (n * k)) : mixedReverseJump P known p z u m.val a = f (reverseSampleOrder p m) := by
    simp only [mixedReverseJump, dif_pos m.is_lt]
    rfl
  calc
    _ = ∑ m ∈ Finset.range (n * k), mixedReverseJump P known p z u m a := by
      simp only [mixedReverseProcess, Nat.min_self, Finset.sum_apply]
    _ = ∑ m : Fin (n * k), mixedReverseJump P known p z u m.val a :=
      (Fin.sum_univ_eq_sum_range (fun m => mixedReverseJump P known p z u m a) (n * k)).symm
    _ = ∑ m : Fin (n * k), f (reverseSampleOrder p m) := Finset.sum_congr rfl (fun m _ => hfin m)
    _ = ∑ q : Fin n × Fin k, f q := (reverseSampleOrder p).sum_comp f
    _ = ∑ i : Fin n, ∑ j : Fin k, f (i, j) := Fintype.sum_prod_type f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (mixed_transitionResidual_eq_sample_sum P known z u i a).symm

lemma mixedReverseJump_integrable (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    Integrable (mixedReverseJump (k := k) P known p z u m) (P.trainingCoordinateLaw k) := by
  have hS := mixedReverseProcess_martingale (k := k) P known hbound p hz u horder
  rw [← mixedReverseProcess_increment]
  exact (hS.integrable (m + 1)).sub (hS.integrable m)

lemma mixedReverseJump_integral_zero (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    (∫ a, mixedReverseJump (k := k) P known p z u m a ∂P.trainingCoordinateLaw k) = 0 := by
  calc
    _ = ∫ a, ((P.trainingCoordinateLaw k)[mixedReverseJump P known p z u m | reverseTrainingFiltration p m]) a
        ∂P.trainingCoordinateLaw k := (integral_condExp ((reverseTrainingFiltration (k := k) p).le m)).symm
    _ = 0 := integral_eq_zero_of_ae (mixedReverseJump_condExp_zero P known hbound p hz u horder m)

/-- An individual complete residual is integrable under the actual training law. -/
lemma integrable_mixed_transitionResidual (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (i : Fin n) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i) (P.trainingCoordinateLaw k) := by
  have hfun : (fun a : (Fin n × Fin k) → ℝ =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i) =
      (fun a => ∑ j : Fin k, P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z u i a) (a (i, j))) :=
    funext (mixed_transitionResidual_eq_sample_sum P known z u i)
  rw [hfun]
  apply integrable_finsetSum
  intro j _
  rw [← mixedReverseJump_at_coordinate P known p z u (i, j)]
  exact mixedReverseJump_integrable P known hbound p hz u horder _

/-- Fixed-scalar individual centering; the current row's exclusion is essential. -/
theorem integral_mixed_transitionResidual_zero (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (i : Fin n) :
    (∫ a : (Fin n × Fin k) → ℝ,
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i
      ∂P.trainingCoordinateLaw k) = 0 := by
  have hfun : (fun a : (Fin n × Fin k) → ℝ =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i) =
      (fun a => ∑ j : Fin k, P.mixedPremiumJump known k i (mixedArrivalContinuation P known 1 z u i a) (a (i, j))) :=
    funext (mixed_transitionResidual_eq_sample_sum P known z u i)
  rw [hfun, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    rw [← mixedReverseJump_at_coordinate P known p z u (i, j)]
    exact mixedReverseJump_integral_zero P known hbound p hz u horder _
  · intro j _
    rw [← mixedReverseJump_at_coordinate P known p z u (i, j)]
    exact mixedReverseJump_integrable P known hbound p hz u horder _

/-- Clock-conditional reach weights of a training-independent policy may be fixed
here. A selector depending on training is not substituted into this identity. -/
theorem integral_weighted_mixed_transitionResidual_zero (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (r : Fin n → ℝ) :
    (∫ a : (Fin n × Fin k) → ℝ, ∑ i : Fin n,
      r i * (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i
      ∂P.trainingCoordinateLaw k) = 0 := by
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul, integral_mixed_transitionResidual_zero P known hbound p hz u horder i, mul_zero]
  · intro i _
    exact (integrable_mixed_transitionResidual P known hbound p hz u horder i).const_mul (r i)

end ProphetSecretary.Model
