import ProphetSecretary.Statistics.MixedEmpiricalSlopeMaximalMoments
import ProphetSecretary.Statistics.MixedEmpiricalSuffixBridge
import ProphetSecretary.Statistics.EmpiricalSlopeSuffixBridge

/-!
# Mixed scalar-increment suffixes are reverse block endpoints

The deterministic comparison preserves original identities and all sample rows.
Every known residual and known jump is zero. No sorting selection is supplied
to the policy; the correspondence holds for each actual strict clock order.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma mixedSlopeResidual_suffix_eq_block (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    (a : (Fin n × Fin k) → ℝ) (i : Fin n) :
    ProphetSecretary.Statistics.suffixSum u (fun j =>
      ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u j -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z' u j) / (z' - z)) (some i) =
      mixedSlopeReverseProcess P known p z z' u ((n - (p.symm i).val) * k) a := by
  let r := n - (p.symm i).val
  have hr : r ≤ n := Nat.sub_le n _
  have heq (c : ℝ) : ProphetSecretary.Statistics.suffixSum u
      ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 c u) (some i) =
      mixedReverseProcess P known p c u (r * k) a :=
    (ProphetSecretary.Statistics.clock_suffix_eq_reverse_prefix u _ p horder i).trans
      (mixedReverseProcess_block_endpoint P known p c u a hr).symm
  rw [ProphetSecretary.Statistics.suffixSum_sub_div, heq z, heq z']
  rfl

theorem mixedResidualSlopeSuffixEnvelope_le_reverseMaximum (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    (a : (Fin n × Fin k) → ℝ) :
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ≤
      mixedSlopeReverseMaximum P known p z z' u a := by
  change (Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (fun j : Option (Fin n) =>
    |ProphetSecretary.Statistics.suffixSum u (fun i =>
      ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z' u i) / (z' - z)) j|)) ≤ _
  apply Finset.sup'_le
  intro j _
  cases j with
  | none =>
    rw [ProphetSecretary.Statistics.suffixSum_sub_div]
    simp only [ProphetSecretary.Statistics.suffixSum]
    rw [← mixedReverseProcess_terminal_eq_residual_sum P known p z u a,
      ← mixedReverseProcess_terminal_eq_residual_sum P known p z' u a]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |mixedSlopeReverseProcess P known p z z' u m a|) (le_refl (n * k))
  | some i =>
    rw [mixedSlopeResidual_suffix_eq_block P known p z z' u horder a i]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |mixedSlopeReverseProcess P known p z z' u m a|)
      (Nat.mul_le_mul_right k (Nat.sub_le n _))

end ProphetSecretary.Model
