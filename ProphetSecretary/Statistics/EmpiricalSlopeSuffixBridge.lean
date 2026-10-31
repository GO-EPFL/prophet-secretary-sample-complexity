import ProphetSecretary.Statistics.EmpiricalSlopeMaximalMoments
import ProphetSecretary.Statistics.EmpiricalSuffixBridge

/-!
# Scalar-increment suffixes and sample block endpoints

Every arrival suffix of the normalized residual difference is an endpoint of the
constructed difference martingale. This comparison is pointwise in the complete
sample array; it requires no measurable selection of a clock-sorting permutation.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics

variable {n : ℕ}

lemma suffixSum_sub_div (u f g : Fin n → ℝ) (d : ℝ) (j : Option (Fin n)) :
    suffixSum u (fun i => (f i - g i) / d) j = (suffixSum u f j - suffixSum u g j) / d := by
  cases j with
  | none => simp only [suffixSum, div_eq_mul_inv, Finset.sum_mul, Finset.sum_sub_distrib, sub_mul]
  | some j =>
    simp only [suffixSum]
    calc
      _ = ∑ i : Fin n, ((if u j ≤ u i then f i else 0) - (if u j ≤ u i then g i else 0)) / d := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul, Finset.sum_sub_distrib, sub_mul]

lemma suffixEnvelope_sub_div_le (u f g : Fin n → ℝ) {d : ℝ} (hd : 0 < d) :
    suffixEnvelope u (fun i => (f i - g i) / d) ≤ (suffixEnvelope u f + suffixEnvelope u g) / d := by
  apply Finset.sup'_le
  intro j _
  rw [suffixSum_sub_div, abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  exact (abs_sub _ _).trans (add_le_add (le_suffixEnvelope u f j) (le_suffixEnvelope u g j))

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def Instance.residualSlopeSuffixEnvelope (Q P : Instance n) (z z' : ℝ) (u : Fin n → ℝ) : ℝ :=
  ProphetSecretary.Statistics.suffixEnvelope u (fun i => (Q.transitionResidual P 1 z u i - Q.transitionResidual P 1 z' u i) / (z' - z))

lemma empiricalSlopeResidual_suffix_eq_block (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    (a : (Fin n × Fin k) → ℝ) (i : Fin n) :
    ProphetSecretary.Statistics.suffixSum u (fun j =>
      ((totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u j -
       (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z' u j) / (z' - z)) (some i) =
      empiricalSlopeReverseProcess P p z z' u ((n - (p.symm i).val) * k) a := by
  let r := n - (p.symm i).val
  have hr : r ≤ n := Nat.sub_le n _
  have heq (c : ℝ) : ProphetSecretary.Statistics.suffixSum u
      ((totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 c u) (some i) =
      empiricalReverseProcess P p c u (r * k) a :=
    (ProphetSecretary.Statistics.clock_suffix_eq_reverse_prefix u _ p horder i).trans
      (empiricalReverseProcess_block_endpoint P p c u a hr).symm
  rw [ProphetSecretary.Statistics.suffixSum_sub_div, heq z, heq z']
  rfl

theorem empiricalResidualSlopeSuffixEnvelope_le_reverseMaximum (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    (a : (Fin n × Fin k) → ℝ) :
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ≤
      empiricalSlopeReverseMaximum P p z z' u a := by
  change (Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (fun j : Option (Fin n) =>
    |ProphetSecretary.Statistics.suffixSum u (fun i =>
      ((totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i -
       (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z' u i) / (z' - z)) j|)) ≤ _
  apply Finset.sup'_le
  intro j _
  cases j with
  | none =>
    rw [ProphetSecretary.Statistics.suffixSum_sub_div]
    simp only [ProphetSecretary.Statistics.suffixSum]
    rw [← empiricalReverseProcess_terminal_eq_residual_sum P p z u a,
      ← empiricalReverseProcess_terminal_eq_residual_sum P p z' u a]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |empiricalSlopeReverseProcess P p z z' u m a|) (le_refl (n * k))
  | some i =>
    rw [empiricalSlopeResidual_suffix_eq_block P p z z' u horder a i]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |empiricalSlopeReverseProcess P p z z' u m a|)
      (Nat.mul_le_mul_right k (Nat.sub_le n _))

end ProphetSecretary.Model
