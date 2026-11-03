import ProphetSecretary.Analysis.MultilevelSeedMap

/-!
# The number of random draws in a multilevel tree

A fixed level has a deterministic number of seed slots. Two consecutive
counts suffice to compute the next count, so planning the storage does
not traverse the estimator tree.
-/

open scoped BigOperators

namespace ProphetSecretary.Analysis

def multilevelSeedSlotPair : ℕ → (ℕ × ℕ) × ℕ
  | 0 => ((0, 4), 1)
  | r + 1 =>
    let q := multilevelSeedSlotPair r
    ((q.1.2, 8 * q.1.2 + 4 * q.1.1 + 4), q.2 + 6)

def multilevelSeedSlots (r : ℕ) : ℕ := (multilevelSeedSlotPair r).1.1

lemma multilevelSeedSlotPair_work (r : ℕ) :
    (multilevelSeedSlotPair r).2 = 1 + 6 * r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [multilevelSeedSlotPair, ih]
    omega

lemma multilevelSeedSlots_zero : multilevelSeedSlots 0 = 0 := rfl

lemma multilevelSeedSlots_one : multilevelSeedSlots 1 = 4 := rfl

lemma multilevelSeedSlots_succ_succ (r : ℕ) :
    multilevelSeedSlots (r + 2) = 8 * multilevelSeedSlots (r + 1) + 4 * multilevelSeedSlots r + 4 := rfl

lemma multilevelSeedSlots_split (r : ℕ) :
    multilevelSeedSlots (r + 1) = 4 ^ (r + 1) +
      ∑ l : Fin r, 4 ^ (r - l.val) * (1 + multilevelSeedSlots (l.val + 1) + multilevelSeedSlots l.val) := by
  induction r with
  | zero => simp [multilevelSeedSlots_one]
  | succ r ih =>
    rw [multilevelSeedSlots_succ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel_left]
    have hShift (l : Fin r) : r + 1 - l.val = r - l.val + 1 := by omega
    simp_rw [hShift, pow_succ]
    rw [show (∑ l : Fin r, 4 ^ (r - l.val) * 4 *
            (1 + multilevelSeedSlots (l.val + 1) + multilevelSeedSlots l.val)) =
          4 * ∑ l : Fin r, 4 ^ (r - l.val) *
            (1 + multilevelSeedSlots (l.val + 1) + multilevelSeedSlots l.val) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring]
    omega

theorem multilevelSeedSlots_eq_seedCount {Seed : Type*}
    (r : ℕ) (t : MultilevelTree Seed r) :
    multilevelSeedSlots r = multilevelTreeSeedCount r t := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases t with
    | zero => simp [multilevelSeedSlots_zero, multilevelTreeSeedCount]
    | @node d base tr up lo =>
      rw [multilevelSeedSlots_split, multilevelTreeSeedCount]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      have hu (j : Fin (4 ^ (d - l.val))) :=
        ih (l.val + 1) (by have := l.isLt; omega) (up l j)
      have hl (j : Fin (4 ^ (d - l.val))) :=
        ih l.val (by have := l.isLt; omega) (lo l j)
      simp_rw [← hu, ← hl]
      simp

private def constantMultilevelTree {Seed : Type*} (s : Seed) : (r : ℕ) → MultilevelTree Seed r
  | 0 => .zero
  | r + 1 => .node (fun _ => s) (fun _ _ => s)
      (fun l _ => constantMultilevelTree s (l.val + 1))
      (fun l _ => constantMultilevelTree s l.val)
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

theorem multilevelSeedSlots_le (r : ℕ) : multilevelSeedSlots r ≤ 4 * 16 ^ r := by
  rw [multilevelSeedSlots_eq_seedCount r (constantMultilevelTree () r)]
  exact multilevelTreeSeedCount_le _ _

end ProphetSecretary.Analysis
