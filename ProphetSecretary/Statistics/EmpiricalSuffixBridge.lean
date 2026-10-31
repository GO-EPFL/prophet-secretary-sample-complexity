import ProphetSecretary.Statistics.EmpiricalReverseMaximalMoments
import ProphetSecretary.Statistics.EmpiricalCompleteResidual
import ProphetSecretary.Statistics.ResidualComparison

/-!
# Arrival suffixes as reverse sample blocks

Every complete arrival suffix is a block endpoint of the sample-by-sample reverse
process. This deterministic correspondence preserves the original identities and
therefore compares the paper's suffix envelope with the actual martingale maximum.
No measurable sorting choice is required: the identities hold for every strict order.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics

lemma sum_fin_prefix_castLE {n r : ℕ} (hr : r ≤ n) (f : Fin n → ℝ) :
    (∑ j : Fin r, f (Fin.castLE hr j)) = ∑ j : Fin n, if j.val < r then f j else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => Fin.castLE hr j)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.is_lt⟩
  · intro j _ j' _ he
    exact Fin.ext (congrArg (fun q : Fin n => q.val) he)
  · intro j hj
    refine ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro j _
    rfl

lemma clock_suffix_eq_reverse_prefix {n : ℕ} (u ξ : Fin n → ℝ) (p : Equiv.Perm (Fin n))
    (horder : ProphetSecretary.Model.Instance.HasArrivalOrder u p) (i : Fin n) :
    suffixSum u ξ (some i) =
      ∑ j : Fin n, if j.val < n - (p.symm i).val then ξ (p j.rev) else 0 := by
  have hmono : StrictMono (fun j : Fin n => u (p j)) := horder
  have hiff (j : Fin n) : u i ≤ u (p j) ↔ p.symm i ≤ j := by
    simpa only [p.apply_symm_apply] using (hmono.le_iff_le : u (p (p.symm i)) ≤ u (p j) ↔ p.symm i ≤ j)
  have hrev (j : Fin n) : p.symm i ≤ j.rev ↔ j.val < n - (p.symm i).val := by
    change (p.symm i).val ≤ j.rev.val ↔ j.val < n - (p.symm i).val
    dsimp only [Fin.rev]
    have hj := j.is_lt
    have hi := (p.symm i).is_lt
    omega
  calc
    suffixSum u ξ (some i) = ∑ j : Fin n, if u i ≤ u (p j) then ξ (p j) else 0 :=
      (Equiv.sum_comp p (fun j => if u i ≤ u j then ξ j else 0)).symm
    _ = ∑ j : Fin n, if p.symm i ≤ j then ξ (p j) else 0 :=
      Finset.sum_congr rfl (fun j _ => by simp only [hiff j])
    _ = ∑ j : Fin n, if p.symm i ≤ j.rev then ξ (p j.rev) else 0 :=
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun j => if p.symm i ≤ j then ξ (p j) else 0)).symm
    _ = _ := Finset.sum_congr rfl (fun j _ => by simp only [hrev j])

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- A block endpoint contains the first `r` reverse-arrival marginals, each with
all `k` samples. The reverse identity is still taken in the original `Fin n`. -/
lemma empiricalReverseProcess_block_endpoint (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) {r : ℕ} (hr : r ≤ n) :
    empiricalReverseProcess P p z u (r * k) a =
      ∑ j : Fin n, if j.val < r then
        (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u (p j.rev) else 0 := by
  have hrk : r * k ≤ n * k := Nat.mul_le_mul_right k hr
  let f : Fin r × Fin k → ℝ := fun q =>
    P.empiricalPremiumJump k (p (Fin.castLE hr q.1).rev)
      (empiricalArrivalContinuation 1 z u (p (Fin.castLE hr q.1).rev) a)
      (a (p (Fin.castLE hr q.1).rev, q.2))
  have hfin (m : Fin (r * k)) : empiricalReverseJump P p z u m.val a = f (finProdFinEquiv.symm m) := by
    have hm : m.val < n * k := m.is_lt.trans_le hrk
    rw [empiricalReverseJump, dif_pos hm]
    rfl
  calc
    _ = ∑ m ∈ Finset.range (r * k), empiricalReverseJump P p z u m a := by
      simp only [empiricalReverseProcess, Nat.min_eq_left hrk, Finset.sum_apply]
    _ = ∑ m : Fin (r * k), empiricalReverseJump P p z u m.val a :=
      (Fin.sum_univ_eq_sum_range (fun m => empiricalReverseJump P p z u m a) (r * k)).symm
    _ = ∑ m : Fin (r * k), f (finProdFinEquiv.symm m) := Finset.sum_congr rfl (fun m _ => hfin m)
    _ = ∑ q : Fin r × Fin k, f q := finProdFinEquiv.symm.sum_comp f
    _ = ∑ j : Fin r, ∑ l : Fin k, f (j, l) := Fintype.sum_prod_type f
    _ = ∑ j : Fin r,
        (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u (p (Fin.castLE hr j).rev) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (empirical_transitionResidual_eq_sample_sum P z u (p (Fin.castLE hr j).rev) a).symm
    _ = _ := ProphetSecretary.Statistics.sum_fin_prefix_castLE hr (fun j =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u (p j.rev))

/-- The manuscript's complete-path residual suffix maximum is dominated pointwise
by the constructed sample martingale maximum. This statement does not average training. -/
theorem empiricalResidualSuffixEnvelope_le_reverseMaximum (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (a : (Fin n × Fin k) → ℝ) :
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ≤
      empiricalReverseMaximum P p z u a := by
  let ξ : Fin n → ℝ := (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u
  change (Finset.univ.sup' ⟨none, Finset.mem_univ _⟩
    (fun j : Option (Fin n) => |ProphetSecretary.Statistics.suffixSum u ξ j|)) ≤ _
  apply Finset.sup'_le
  intro j _
  cases j with
  | none =>
    change |∑ i : Fin n, (totalEmpiricalInstance (reservoirCoordinates.symm a)).transitionResidual P 1 z u i| ≤ _
    rw [← empiricalReverseProcess_terminal_eq_residual_sum P p z u a]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |empiricalReverseProcess P p z u m a|) (le_refl (n * k))
  | some i =>
    let r := n - (p.symm i).val
    have hr : r ≤ n := Nat.sub_le n _
    have hs := ProphetSecretary.Statistics.clock_suffix_eq_reverse_prefix u ξ p horder i
    have hb := empiricalReverseProcess_block_endpoint P p z u a hr
    have he : ProphetSecretary.Statistics.suffixSum u ξ (some i) = empiricalReverseProcess P p z u (r * k) a :=
      hs.trans hb.symm
    rw [he]
    exact ProphetSecretary.Probability.le_runningMaximum
      (fun m => |empiricalReverseProcess P p z u m a|) (Nat.mul_le_mul_right k hr)

end ProphetSecretary.Model
