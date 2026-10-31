import ProphetSecretary.Statistics.MixedEmpiricalReverseMaximalMoments
import ProphetSecretary.Statistics.MixedEmpiricalCompleteResidual
import ProphetSecretary.Statistics.EmpiricalSuffixBridge

/-!
# Mixed-law residual suffixes are reverse sample block endpoints

Known marginals contribute zero to both sides. The deterministic correspondence
keeps the original identity labels and applies for every strict clock order.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- A block endpoint contains the first `r` reverse-arrival marginals, each with
all `k` samples. The reverse identity is still taken in the original `Fin n`. -/
lemma mixedReverseProcess_block_endpoint (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) {r : ℕ} (hr : r ≤ n) :
    mixedReverseProcess P known p z u (r * k) a =
      ∑ j : Fin n, if j.val < r then
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u (p j.rev) else 0 := by
  have hrk : r * k ≤ n * k := Nat.mul_le_mul_right k hr
  let f : Fin r × Fin k → ℝ := fun q =>
    P.mixedPremiumJump known k (p (Fin.castLE hr q.1).rev)
      (mixedArrivalContinuation P known 1 z u (p (Fin.castLE hr q.1).rev) a)
      (a (p (Fin.castLE hr q.1).rev, q.2))
  have hfin (m : Fin (r * k)) : mixedReverseJump P known p z u m.val a = f (finProdFinEquiv.symm m) := by
    have hm : m.val < n * k := m.is_lt.trans_le hrk
    rw [mixedReverseJump, dif_pos hm]
    rfl
  calc
    _ = ∑ m ∈ Finset.range (r * k), mixedReverseJump P known p z u m a := by
      simp only [mixedReverseProcess, Nat.min_eq_left hrk, Finset.sum_apply]
    _ = ∑ m : Fin (r * k), mixedReverseJump P known p z u m.val a :=
      (Fin.sum_univ_eq_sum_range (fun m => mixedReverseJump P known p z u m a) (r * k)).symm
    _ = ∑ m : Fin (r * k), f (finProdFinEquiv.symm m) := Finset.sum_congr rfl (fun m _ => hfin m)
    _ = ∑ q : Fin r × Fin k, f q := finProdFinEquiv.symm.sum_comp f
    _ = ∑ j : Fin r, ∑ l : Fin k, f (j, l) := Fintype.sum_prod_type f
    _ = ∑ j : Fin r,
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u (p (Fin.castLE hr j).rev) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (mixed_transitionResidual_eq_sample_sum P known z u (p (Fin.castLE hr j).rev) a).symm
    _ = _ := ProphetSecretary.Statistics.sum_fin_prefix_castLE hr (fun j =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u (p j.rev))

/-- The manuscript's complete-path residual suffix maximum is dominated pointwise
by the constructed sample martingale maximum. This statement does not average training. -/
theorem mixedResidualSuffixEnvelope_le_reverseMaximum (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (a : (Fin n × Fin k) → ℝ) :
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ≤
      mixedReverseMaximum P known p z u a := by
  let ξ : Fin n → ℝ := (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u
  change (Finset.univ.sup' ⟨none, Finset.mem_univ _⟩
    (fun j : Option (Fin n) => |ProphetSecretary.Statistics.suffixSum u ξ j|)) ≤ _
  apply Finset.sup'_le
  intro j _
  cases j with
  | none =>
    change |∑ i : Fin n, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).transitionResidual P 1 z u i| ≤ _
    rw [← mixedReverseProcess_terminal_eq_residual_sum P known p z u a]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |mixedReverseProcess P known p z u m a|) (le_refl (n * k))
  | some i =>
    let r := n - (p.symm i).val
    have hr : r ≤ n := Nat.sub_le n _
    have hs := ProphetSecretary.Statistics.clock_suffix_eq_reverse_prefix u ξ p horder i
    have hb := mixedReverseProcess_block_endpoint P known p z u a hr
    have he : ProphetSecretary.Statistics.suffixSum u ξ (some i) = mixedReverseProcess P known p z u (r * k) a :=
      hs.trans hb.symm
    rw [he]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |mixedReverseProcess P known p z u m a|) (Nat.mul_le_mul_right k hr)

end ProphetSecretary.Model
