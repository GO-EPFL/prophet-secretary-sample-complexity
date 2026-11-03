import ProphetSecretary.Analysis.RationalHeight
import ProphetSecretary.Analysis.MultilevelEstimator

/-!
# Rational size through multilevel trees

Each payoff evaluation increases the height of its recursive argument by
an additive amount. The two recursive arguments of a paired difference
have distinct subtrees. Hence height is linear in the tree work bound.
-/

open scoped BigOperators

namespace ProphetSecretary.Analysis

lemma rationalHeight_four : RationalHeight 4 2 := by unfold RationalHeight; decide

lemma rationalHeight_five : RationalHeight 5 3 := by unfold RationalHeight; decide

lemma rationalHeight_clipFive {a : ℚ} {B : ℕ} (ha : RationalHeight a B) :
    RationalHeight (clipFive a) (max 3 B) := by
  simpa only [clipFive, Nat.zero_le, max_eq_right] using
    rationalHeight_zero.max (rationalHeight_five.min ha)

lemma rationalHeight_averageCoefficient (d : ℕ) : RationalHeight (1/(4:ℚ)^d) (2*d) := by
  have h := rationalHeight_one.div (rationalHeight_four.pow d)
  simpa only [Nat.zero_add, Nat.mul_comm] using h

private lemma sum_height_charge {K : ℕ} (hK : 1 ≤ K) (t : Fin K → ℕ)
    (C a b : ℕ) (h : a+b ≤ C) :
    (∑ j, (C*t j+a)) + b ≤ ∑ j, C*(1+t j) := by
  simp only [Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have hb : b ≤ K*b := Nat.le_mul_of_pos_left _ hK
  have hm := Nat.mul_le_mul_left K h
  rw [Nat.mul_add] at hm
  omega

/-- Bit lengths of the recursive estimate, with an invariant indexed by the
remaining level. A payoff must use its recursive estimate with additive
height growth; a generic multiplication of two copies would not suffice. -/
theorem multilevelEstimate_rationalHeight {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℚ) (G : ℕ → State → Prop) (R B : ℕ)
    (hBase : ∀ r x, r ≤ R → G r x → RationalHeight (D.emptyValue x) B ∧
      RationalHeight (D.offset x) B ∧ RationalHeight (D.coefficient x) B)
    (hPay : ∀ r x s a A, r ≤ R → G r x → RationalHeight a A →
      RationalHeight (D.payoff x (D.sample x s) a) (B+A))
    (hChild : ∀ r x s j, r ≤ R → G r x → D.isEmpty x = false → j < r →
      G j (D.child x (D.sample x s)))
    (r : ℕ) (hr : r ≤ R) (x : State) (hx : G r x) (t : MultilevelTree Seed r) :
    RationalHeight (multilevelEstimate D r x t) (16*(B+R+1)*multilevelTreeWork r t) := by
  let C := 16*(B+R+1)
  change RationalHeight (multilevelEstimate D r x t) (C*multilevelTreeWork r t)
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero =>
      rw [multilevelEstimate_zero]
      exact rationalHeight_zero.mono (Nat.zero_le _)
    | @node d base tr up lo =>
      cases he : D.isEmpty x
      · let basePay := fun j : Fin (4^(d+1)) => D.payoff x (D.sample x (base j)) 0
        let U := fun (l : Fin d) j => multilevelTreeWork (l.val+1) (up l j)
        let L := fun (l : Fin d) j => multilevelTreeWork l.val (lo l j)
        let A := fun (l : Fin d) j => D.child x (D.sample x (tr l j))
        let diff := fun (l : Fin d) j =>
          D.payoff x (D.sample x (tr l j)) (multilevelEstimate D (l.val+1) (A l j) (up l j)) -
          D.payoff x (D.sample x (tr l j)) (multilevelEstimate D l.val (A l j) (lo l j))
        let baseAvg := (1/(4:ℚ)^(d+1)) * ∑ j, basePay j
        let avg := fun l : Fin d => (1/(4:ℚ)^(d-l.val)) * ∑ j, diff l j
        let P := ∑ l : Fin d, ∑ j : Fin (4^(d-l.val)), (1+U l j+L l j)
        have hBasePay (j : Fin (4^(d+1))) : RationalHeight (basePay j) B := by
          simpa only [Nat.add_zero] using hPay _ x (base j) 0 0 hr hx rationalHeight_zero
        have hB := (rationalHeight_averageCoefficient (d+1)).mul
          (rationalHeight_sum Finset.univ basePay (fun _ => B) (fun j _ => hBasePay j))
        have hBaseAvg : RationalHeight baseAvg (C*4^(d+1)) := by
          refine hB.mono ?_
          have hc := sum_height_charge (K := 4^(d+1)) (Nat.succ_le_of_lt (by positivity)) (fun _ => 0)
            C (B+1) (2*(d+1)) (by dsimp [C]; omega)
          simp only [mul_zero, zero_add, Nat.add_zero, Nat.mul_one, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hc ⊢
          rw [Nat.mul_comm (4^(d+1)) C] at hc
          omega
        have hDiff (l : Fin d) (j : Fin (4^(d-l.val))) :
            RationalHeight (diff l j) (C*(U l j+L l j)+(2*B+1)) := by
          have hu : l.val+1 < d+1 := by have := l.isLt; omega
          have hl : l.val < d+1 := by have := l.isLt; omega
          have hU := ih (l.val+1) hu (hu.le.trans hr) (A l j) (hChild _ x (tr l j) _ hr hx he hu) (up l j)
          have hL := ih l.val hl (hl.le.trans hr) (A l j) (hChild _ x (tr l j) _ hr hx he hl) (lo l j)
          have h := (hPay _ x (tr l j) _ _ hr hx hU).sub (hPay _ x (tr l j) _ _ hr hx hL)
          exact h.mono (by dsimp [U, L]; rw [Nat.mul_add]; omega)
        let avgHeight := fun l : Fin d => 2*(d-l.val) +
          ∑ j : Fin (4^(d-l.val)), (C*(U l j+L l j)+(2*B+2))
        have hAvg (l : Fin d) : RationalHeight (avg l) (avgHeight l) := by
          have hE (j : Fin (4^(d-l.val))) : C*(U l j+L l j)+(2*B+1)+1 =
              C*(U l j+L l j)+(2*B+2) := by omega
          have h := (rationalHeight_averageCoefficient (d-l.val)).mul
            (rationalHeight_sum Finset.univ (diff l) _ (fun j _ => hDiff l j))
          simpa only [avgHeight, hE] using h
        have hPairSum : RationalHeight (∑ l : Fin d, avg l) (C*P) := by
          refine (rationalHeight_sum Finset.univ avg avgHeight (fun l _ => hAvg l)).mono ?_
          simp only [P, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro l _
          have hc := sum_height_charge (K := 4^(d-l.val)) (Nat.succ_le_of_lt (by positivity)) (fun j => U l j+L l j)
            C (2*B+2) (2*(d-l.val)+1) (by dsimp [C]; omega)
          simp only [avgHeight, Nat.add_assoc]
          omega
        have hQ := hBase _ x hr hx
        have hRaw := hQ.2.1.add (hQ.2.2.mul (hBaseAvg.add hPairSum))
        have hClip := rationalHeight_clipFive hRaw
        simp only [multilevelEstimate, he, Bool.false_eq_true, if_false]
        change RationalHeight (clipFive (D.offset x + D.coefficient x *
          (baseAvg + ∑ l : Fin d, avg l))) _
        apply hClip.mono
        simp only [multilevelTreeWork]
        change max 3 (B + (B + (C*4^(d+1)+C*P+1)) + 1) ≤ C*(1+4^(d+1)+P)
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
        dsimp [C]
        omega
      · rw [multilevelEstimate_empty D d x he]
        apply (hBase _ x hr hx).1.mono
        simp only [multilevelTreeWork]
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
        dsimp [C]
        omega

end ProphetSecretary.Analysis
