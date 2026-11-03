import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational height bounds

`RationalHeight q B` bounds the absolute numerator and the positive
denominator of `q` by `2^B`. Passing to lowest terms never increases either
bound. The arithmetic inequalities also bound the unnormalized integers
formed before reducing a fraction.
-/

open scoped BigOperators

namespace ProphetSecretary.Analysis

def RationalHeight (q : ℚ) (B : ℕ) : Prop := q.num.natAbs ≤ 2^B ∧ q.den ≤ 2^B

lemma RationalHeight.mono {q : ℚ} {a b : ℕ} (h : RationalHeight q a) (hab : a ≤ b) : RationalHeight q b :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by decide) hab), h.2.trans (Nat.pow_le_pow_right (by decide) hab)⟩

lemma rationalHeight_zero : RationalHeight 0 0 := by unfold RationalHeight; decide

lemma rationalHeight_one : RationalHeight 1 0 := by unfold RationalHeight; decide

lemma rationalHeight_intCast (z : ℤ) (B : ℕ) (hz : z.natAbs ≤ 2^B) : RationalHeight z B := by
  refine ⟨by simpa using hz, ?_⟩
  rw [Rat.den_intCast]
  exact Nat.succ_le_of_lt (by positivity)

lemma rationalHeight_natCast (n B : ℕ) (hn : n ≤ 2^B) : RationalHeight n B := by
  refine ⟨by simpa using hn, ?_⟩
  rw [Rat.den_natCast]
  exact Nat.succ_le_of_lt (by positivity)

/-- The canonical positive-denominator representation has no larger
integers than any nonzero-denominator representation of the same number. -/
lemma rationalHeight_of_fraction (a d : ℤ) (hd : d ≠ 0) (B : ℕ)
    (ha : a.natAbs ≤ 2^B) (hD : d.natAbs ≤ 2^B) : RationalHeight ((a:ℚ)/(d:ℚ)) B := by
  let q := (a:ℚ)/(d:ℚ)
  obtain ⟨c,hc₁,hc₂⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hd
  have hc : 1 ≤ c.natAbs := by
    by_contra! hz
    have hz' : c = 0 := Int.natAbs_eq_zero.mp (by omega)
    exact hd (by simpa [hz'] using hc₂)
  have h₁ : a.natAbs = c.natAbs*q.num.natAbs := by
    simpa only [Int.natAbs_mul] using congrArg Int.natAbs hc₁
  have h₂ : d.natAbs = c.natAbs*q.den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hc₂
  exact ⟨(by rw [h₁]; exact Nat.le_mul_of_pos_left _ hc : q.num.natAbs ≤ a.natAbs).trans ha,
    (by rw [h₂]; exact Nat.le_mul_of_pos_left _ hc : q.den ≤ d.natAbs).trans hD⟩

lemma RationalHeight.neg {q : ℚ} {B : ℕ} (h : RationalHeight q B) : RationalHeight (-q) B := by
  simpa only [RationalHeight, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg] using h

lemma RationalHeight.mul {q r : ℚ} {a b : ℕ} (hq : RationalHeight q a) (hr : RationalHeight r b) :
    RationalHeight (q*r) (a+b) := by
  have he : q*r = ((q.num*r.num:ℤ):ℚ)/((q.den*r.den:ℕ):ℚ) := calc
    q*r = ((q.num:ℚ)/q.den)*((r.num:ℚ)/r.den) := congrArg₂ (·*·) q.num_div_den.symm r.num_div_den.symm
    _ = _ := by push_cast; rw [div_mul_div_comm]
  rw [he, ← Int.cast_natCast]
  apply rationalHeight_of_fraction _ _ (by exact_mod_cast (Nat.mul_ne_zero q.den_ne_zero r.den_ne_zero))
  · rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul hq.1 hr.1
  · rw [Int.natAbs_natCast, pow_add]
    exact Nat.mul_le_mul hq.2 hr.2

lemma RationalHeight.add {q r : ℚ} {a b : ℕ} (hq : RationalHeight q a) (hr : RationalHeight r b) :
    RationalHeight (q+r) (a+b+1) := by
  have hqd : (q.den:ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrd : (r.den:ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have he : q+r = ((q.num*r.den+r.num*q.den:ℤ):ℚ)/((q.den*r.den:ℕ):ℚ) := calc
    q+r = ((q.num:ℚ)/q.den)+((r.num:ℚ)/r.den) := congrArg₂ (·+·) q.num_div_den.symm r.num_div_den.symm
    _ = _ := by push_cast; simpa only [mul_comm (q.den:ℚ)] using div_add_div (q.num:ℚ) (r.num:ℚ) hqd hrd
  rw [he, ← Int.cast_natCast]
  apply rationalHeight_of_fraction _ _ (by exact_mod_cast (Nat.mul_ne_zero q.den_ne_zero r.den_ne_zero))
  · calc
      _ ≤ (q.num*(r.den:ℤ)).natAbs + (r.num*(q.den:ℤ)).natAbs := Int.natAbs_add_le _ _
      _ ≤ 2^a*2^b + 2^b*2^a := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = 2^(a+b+1) := by rw [pow_succ, pow_add]; ring
  · rw [Int.natAbs_natCast]
    exact (Nat.mul_le_mul hq.2 hr.2).trans (by rw [pow_succ, pow_add]; omega)

lemma RationalHeight.sub {q r : ℚ} {a b : ℕ} (hq : RationalHeight q a) (hr : RationalHeight r b) :
    RationalHeight (q-r) (a+b+1) := by rw [sub_eq_add_neg]; exact hq.add hr.neg

lemma RationalHeight.inv {q : ℚ} {B : ℕ} (hq : RationalHeight q B) : RationalHeight q⁻¹ B := by
  by_cases hz : q = 0
  · rw [hz, inv_zero]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hz
  have he : q⁻¹ = ((q.den:ℤ):ℚ)/(q.num:ℚ) := calc
    q⁻¹ = (((q.num:ℚ)/q.den)⁻¹) := congrArg Inv.inv q.num_div_den.symm
    _ = _ := by push_cast; exact inv_div _ _
  rw [he]
  exact rationalHeight_of_fraction _ _ hn B (by simpa only [Int.natAbs_natCast] using hq.2) hq.1

lemma RationalHeight.div {q r : ℚ} {a b : ℕ} (hq : RationalHeight q a) (hr : RationalHeight r b) :
    RationalHeight (q/r) (a+b) := by rw [div_eq_mul_inv]; exact hq.mul hr.inv

lemma RationalHeight.min {q r : ℚ} {a b : ℕ} (hq : RationalHeight q a) (hr : RationalHeight r b) :
    RationalHeight (min q r) (max a b) := by
  rcases min_choice q r with h | h
  · rw [h]; exact hq.mono (le_max_left _ _)
  · rw [h]; exact hr.mono (le_max_right _ _)

lemma RationalHeight.max {q r : ℚ} {a b : ℕ} (hq : RationalHeight q a) (hr : RationalHeight r b) :
    RationalHeight (max q r) (max a b) := by
  rcases max_choice q r with h | h
  · rw [h]; exact hq.mono (le_max_left _ _)
  · rw [h]; exact hr.mono (le_max_right _ _)

lemma RationalHeight.pow {q : ℚ} {B : ℕ} (hq : RationalHeight q B) (r : ℕ) :
    RationalHeight (q^r) (r*B) := by
  induction r with
  | zero => simpa using rationalHeight_one
  | succ r ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hq

lemma rationalHeight_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ι → ℕ)
    (hf : ∀ i ∈ s, RationalHeight (f i) (B i)) :
    RationalHeight (∑ i ∈ s, f i) (∑ i ∈ s, (B i+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rationalHeight_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h := (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    exact h.mono (by omega)

lemma rationalHeight_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ι → ℕ)
    (hf : ∀ i ∈ s, RationalHeight (f i) (B i)) :
    RationalHeight (∏ i ∈ s, f i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rationalHeight_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end ProphetSecretary.Analysis
