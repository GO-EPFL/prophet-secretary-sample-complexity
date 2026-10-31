import ProphetSecretary.Statistics.EmpiricalFutureSamples
import ProphetSecretary.Model.Arrival
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Reverse-arrival training revelation

Samples are revealed marginal by marginal in reverse arrival order. Within a marginal,
the sample index increases. Every row used by the current empirical continuation has
therefore already been revealed, while the current sample is still fresh.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ}

/-- Reverse the arrival permutation, then reveal each marginal's sample indices. -/
def reverseSampleOrder (p : Equiv.Perm (Fin n)) : Fin (n * k) ≃ Fin n × Fin k :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr ((Fin.revPerm).trans p) (Equiv.refl (Fin k)))

lemma reverseSampleOrder_apply (p : Equiv.Perm (Fin n)) (m : Fin (n * k)) :
    reverseSampleOrder p m = (p m.divNat.rev, m.modNat) := rfl

lemma reverseSampleOrder_symm (p : Equiv.Perm (Fin n)) (i : Fin n) (j : Fin k) :
    (reverseSampleOrder p).symm (i, j) = finProdFinEquiv ((p.symm i).rev, j) := rfl

/-- Actual chronological state inclusion, with all zero-arrival identities retained
in the history and hence removed from the future continuation when already observed. -/
lemma futureSampleRows_before_reverseStep (p : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (horder : Instance.HasArrivalOrder u p) {m : ℕ} (hm : m < n * k) :
    ∀ q ∈ futureSampleRows u ((reverseSampleOrder (k := k) p ⟨m, hm⟩).1),
      ∀ a : Fin k, (q, a) ∈ ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder p) m := by
  let r : Fin n := (⟨m, hm⟩ : Fin (n * k)).divNat
  change ∀ q ∈ futureSampleRows u (p r.rev), ∀ a : Fin k, _
  intro q hq a
  rw [mem_futureSampleRows] at hq
  have hmono : StrictMono (fun j : Fin n => u (p j)) := horder
  have hle : r.rev ≤ p.symm q := hmono.le_iff_le.mp (by simpa only [p.apply_symm_apply] using hq.2)
  have hne : r.rev ≠ p.symm q := by
    intro h
    have he : p r.rev = q := by simpa only [p.apply_symm_apply] using congrArg p h
    exact hq.1 he.symm
  have hRank : r.rev < p.symm q := lt_of_le_of_ne hle hne
  have hrev : (p.symm q).rev < r := by simpa only [Fin.rev_rev] using (Fin.rev_lt_rev.mpr hRank)
  rw [ProphetSecretary.Probability.mem_coordinatesBefore, reverseSampleOrder_symm]
  change a.val + k * (p.symm q).rev.val < m
  have hblock : a.val + k * (p.symm q).rev.val < k * r.val := by
    calc
      _ < k + k * (p.symm q).rev.val := Nat.add_lt_add_right a.is_lt _
      _ = k * ((p.symm q).rev.val + 1) := by ring
      _ ≤ k * r.val := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hrev)
  have hbase : k * r.val ≤ m := by
    change k * (m / k) ≤ m
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self m k
  exact hblock.trans_le hbase

/-- Every marginal contributes exactly `k` sample coordinates, independently of
the chosen arrival permutation. -/
lemma sum_reverseSampleOrder_rows {M : Type*} [AddCommMonoid M]
    (p : Equiv.Perm (Fin n)) (f : Fin n → M) :
    (∑ m : Fin (n * k), f ((reverseSampleOrder p m).1)) = k • (∑ i : Fin n, f i) := by
  calc
    _ = ∑ q : Fin n × Fin k, f q.1 := (reverseSampleOrder p).sum_comp _
    _ = ∑ i : Fin n, ∑ _j : Fin k, f i := Fintype.sum_prod_type _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_fin]
      rw [Finset.smul_sum]

end ProphetSecretary.Model
