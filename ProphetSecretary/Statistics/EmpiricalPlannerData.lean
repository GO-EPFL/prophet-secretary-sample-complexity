import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Empirical probabilities and positive-excess callbacks

The planner reads stored observations. Its positive probability and its
conditional excess average are finite computations, also over rational
inputs. The identities below include empirically zero marginals.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics

variable {Value : Type*} [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]
variable {m : ℕ}

def positiveObservations (y : Fin m → Value) : Finset (Fin m) :=
  Finset.univ.filter (fun j => 0 < y j)

def empiricalPositiveProbability (y : Fin m → Value) : Value :=
  (positiveObservations y).card / (m : Value)

def empiricalConditionalExcess (y : Fin m → Value) (v : Value) : Value :=
  (∑ j ∈ positiveObservations y, max 0 (y j - v)) / ((positiveObservations y).card : Value)

lemma empiricalPositiveProbability_mem_unit (y : Fin m → Value) :
    0 ≤ empiricalPositiveProbability y ∧ empiricalPositiveProbability y ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    simp [empiricalPositiveProbability, positiveObservations]
  · have hmpos : (0 : Value) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hc : ((positiveObservations y).card : Value) ≤ m := by
      exact_mod_cast ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin m))
    exact ⟨div_nonneg (Nat.cast_nonneg _) hmpos.le, (div_le_one hmpos).mpr hc⟩

lemma empiricalConditionalExcess_nonnegative (y : Fin m → Value) (v : Value) :
    0 ≤ empiricalConditionalExcess y v := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => le_max_left _ _) (Nat.cast_nonneg _)

lemma empiricalConditionalExcess_le_one (y : Fin m → Value) (hy : ∀ j, y j ≤ 1)
    {v : Value} (hv : 0 ≤ v) : empiricalConditionalExcess y v ≤ 1 := by
  by_cases hc : (positiveObservations y).card = 0
  · simp [empiricalConditionalExcess, hc]
  · have hcpos : (0 : Value) < (positiveObservations y).card := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    apply (div_le_one hcpos).mpr
    calc
      (∑ j ∈ positiveObservations y, max 0 (y j - v)) ≤
          ∑ _j ∈ positiveObservations y, (1 : Value) := by
        apply Finset.sum_le_sum
        intro j _
        apply max_le (by norm_num)
        linarith [hy j]
      _ = _ := by simp

private lemma positivePart_sub_le (x a b : Value) :
    max 0 (x - a) ≤ max 0 (x - b) + |a - b| := by
  apply max_le
  · exact add_nonneg (le_max_left _ _) (abs_nonneg _)
  · have hb : b - a ≤ |a - b| := by linarith [neg_abs_le (a - b)]
    linarith [le_max_right (0 : Value) (x - b)]

lemma empiricalConditionalExcess_lipschitz (y : Fin m → Value) (a b : Value) :
    |empiricalConditionalExcess y a - empiricalConditionalExcess y b| ≤ |a - b| := by
  by_cases hc : (positiveObservations y).card = 0
  · simp [empiricalConditionalExcess, hc]
  · have hcpos : (0 : Value) < (positiveObservations y).card := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    have hbound (a b : Value) : empiricalConditionalExcess y a ≤
        empiricalConditionalExcess y b + |a - b| := by
      have hs : (∑ j ∈ positiveObservations y, max 0 (y j - a)) ≤
          (∑ j ∈ positiveObservations y, max 0 (y j - b)) +
            ((positiveObservations y).card : Value) * |a - b| := by
        calc
          _ ≤ ∑ j ∈ positiveObservations y, (max 0 (y j - b) + |a - b|) :=
            Finset.sum_le_sum (fun j _ => positivePart_sub_le (y j) a b)
          _ = _ := by simp [Finset.sum_add_distrib]
      have hd := div_le_div_of_nonneg_right hs hcpos.le
      unfold empiricalConditionalExcess
      convert hd using 1
      field_simp
    exact abs_le.mpr ⟨by have h := hbound b a; rw [abs_sub_comm b a] at h; linarith,
      by have h := hbound a b; linarith⟩

/-- Factoring out the positive probability recovers the whole empirical premium. -/
theorem empiricalPositiveProbability_mul_excess [NeZero m] (y : Fin m → Value)
    {v : Value} (hv : 0 ≤ v) :
    empiricalPositiveProbability y * empiricalConditionalExcess y v =
      (∑ j : Fin m, max 0 (y j - v)) / (m : Value) := by
  have hsum : (∑ j ∈ positiveObservations y, max 0 (y j - v)) =
      ∑ j : Fin m, max 0 (y j - v) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hn : y j ≤ 0 := by
      by_contra h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
    exact max_eq_left (by linarith)
  by_cases hc : (positiveObservations y).card = 0
  · have hz : ∑ j : Fin m, max 0 (y j - v) = 0 := by
      rw [← hsum, Finset.card_eq_zero.mp hc]
      simp
    simp [empiricalPositiveProbability, empiricalConditionalExcess, hc, hz]
  · unfold empiricalPositiveProbability empiricalConditionalExcess
    rw [hsum]
    have hcn : ((positiveObservations y).card : Value) ≠ 0 := by exact_mod_cast hc
    field_simp

end ProphetSecretary.Statistics
