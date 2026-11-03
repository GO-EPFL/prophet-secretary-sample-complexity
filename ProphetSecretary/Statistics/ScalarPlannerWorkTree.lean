import ProphetSecretary.Analysis.MultilevelEstimator
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counted evaluation of multilevel trees

Each summand is evaluated once. A paired summand shares its transition and
child state, then evaluates the two recursive trees separately. The counters
include generating the finite iteration sizes, forming averages, and clipping.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {Value : Type*}

def countedFiniteSum [AddMonoid Value] {n : ℕ} (f : Fin n → Value × ℕ) : Value × ℕ :=
  let out := List.ofFn f
  ((out.map Prod.fst).sum, (out.map Prod.snd).sum + 8 * n + 1)

lemma countedFiniteSum_value [AddCommMonoid Value] {n : ℕ} (f : Fin n → Value × ℕ) :
    (countedFiniteSum f).1 = ∑ i, (f i).1 := by
  simp only [countedFiniteSum, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

lemma countedFiniteSum_work [AddMonoid Value] {n : ℕ} (f : Fin n → Value × ℕ) :
    (countedFiniteSum f).2 = (∑ i, (f i).2) + 8 * n + 1 := by
  simp only [countedFiniteSum, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def countedFourPower [Field Value] : ℕ → (ℕ × Value) × ℕ
  | 0 => ((1, 1), 2)
  | d + 1 =>
      let q := countedFourPower d
      ((q.1.1 * 4, q.1.2 * 4), q.2 + 4)

lemma countedFourPower_nat [Field Value] (d : ℕ) : (countedFourPower (Value := Value) d).1.1 = 4 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [countedFourPower, ih, Nat.pow_succ]

lemma countedFourPower_value [Field Value] (d : ℕ) : (countedFourPower d).1.2 = (4 : Value) ^ d := by
  induction d with
  | zero => simp [countedFourPower]
  | succ d ih => simp only [countedFourPower, ih, pow_succ]

lemma countedFourPower_work [Field Value] (d : ℕ) : (countedFourPower (Value := Value) d).2 = 2 + 4 * d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [countedFourPower, ih]
    omega

lemma level_add_one_le_four_power (d : ℕ) : d + 1 ≤ 4 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih => rw [Nat.pow_succ]; omega

def countedMultilevelAverage [Field Value] (d : ℕ) (f : Fin (4 ^ d) → Value × ℕ) : Value × ℕ :=
  let q := countedFourPower (Value := Value) d
  let s := countedFiniteSum (fun i : Fin q.1.1 => f (Fin.cast (countedFourPower_nat (Value := Value) d) i))
  ((1 / q.1.2) * s.1, q.2 + s.2 + 3)

lemma countedMultilevelAverage_value [Field Value] (d : ℕ) (f : Fin (4 ^ d) → Value × ℕ) :
    (countedMultilevelAverage d f).1 = (1 / ((4 : Value) ^ d)) * ∑ j, (f j).1 := by
  simp only [countedMultilevelAverage, countedFiniteSum_value, countedFourPower_value]
  congr 1
  exact (finCongr (countedFourPower_nat (Value := Value) d)).sum_comp (fun j => (f j).1)

lemma countedMultilevelAverage_work [Field Value] (d : ℕ) (f : Fin (4 ^ d) → Value × ℕ) :
    (countedMultilevelAverage d f).2 ≤ (∑ j, (f j).2) + 20 * 4 ^ d := by
  have hs := (finCongr (countedFourPower_nat (Value := Value) d)).sum_comp (fun j => (f j).2)
  change (∑ i : Fin (countedFourPower (Value := Value) d).1.1,
    (f (Fin.cast (countedFourPower_nat (Value := Value) d) i)).2) = _ at hs
  simp only [countedMultilevelAverage, countedFiniteSum_work, hs]
  rw [countedFourPower_work, countedFourPower_nat]
  have h := level_add_one_le_four_power d
  omega

lemma countedMultilevelAverage_work_le [Field Value] (d : ℕ) (f : Fin (4 ^ d) → Value × ℕ)
    (g : Fin (4 ^ d) → ℕ) (C : ℕ) (h : ∀ j, (f j).2 ≤ g j + C) :
    (countedMultilevelAverage d f).2 ≤ (∑ j, g j) + (C + 20) * 4 ^ d := by
  calc
    _ ≤ (∑ j, (f j).2) + 20 * 4 ^ d := countedMultilevelAverage_work d f
    _ ≤ (∑ j, (g j + C)) + 20 * 4 ^ d :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun j _ => h j)) _
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring

structure CountedPlannerNode (Context Value : Type*) where
  context : Context
  empty : Bool
  emptyValue : Value
  offset : Value
  coefficient : Value

structure CountedPlannerRecursion (State Context Seed Transition Value : Type*) where
  prepare : State → CountedPlannerNode Context Value × ℕ
  sample : Context → Seed → Transition × ℕ
  child : Context → Transition → State × ℕ
  payoff : Context → Transition → Value → Value × ℕ

namespace CountedPlannerRecursion

variable {State Context Seed Transition : Type*}

def toRecursion (D : CountedPlannerRecursion State Context Seed Transition Value) :
    MultilevelRecursion State Seed Transition Value where
  isEmpty x := (D.prepare x).1.empty
  emptyValue x := (D.prepare x).1.emptyValue
  offset x := (D.prepare x).1.offset
  coefficient x := (D.prepare x).1.coefficient
  sample x s := (D.sample (D.prepare x).1.context s).1
  child x o := (D.child (D.prepare x).1.context o).1
  payoff x o a := (D.payoff (D.prepare x).1.context o a).1

/-- Evaluate the prescribed arithmetic program, storing each transition
and each recursive result before taking its paired difference. -/
def estimate [Field Value] [LinearOrder Value] (D : CountedPlannerRecursion State Context Seed Transition Value) :
    (r : ℕ) → State → MultilevelTree Seed r → Value × ℕ
  | 0, _, .zero => (0, 1)
  | r + 1, x, .node base transition upper lower =>
      let prepared := D.prepare x
      let q := prepared.1
      if q.empty then (q.emptyValue, prepared.2 + 2) else
      let b := countedMultilevelAverage (r + 1) (fun j =>
        let y := D.sample q.context (base j)
        let pay := D.payoff q.context y.1 0
        (pay.1, y.2 + pay.2 + 1))
      let pairs := countedFiniteSum (fun l : Fin r =>
        countedMultilevelAverage (r - l.val) (fun j =>
          let y := D.sample q.context (transition l j)
          let child := D.child q.context y.1
          let plus := estimate D (l.val + 1) child.1 (upper l j)
          let minus := estimate D l.val child.1 (lower l j)
          let payPlus := D.payoff q.context y.1 plus.1
          let payMinus := D.payoff q.context y.1 minus.1
          (payPlus.1 - payMinus.1, y.2 + child.2 + plus.2 + minus.2 + payPlus.2 + payMinus.2 + 3)))
      (clipFive (q.offset + q.coefficient * (b.1 + pairs.1)), prepared.2 + b.2 + pairs.2 + 16)
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

/-- Erasing the counters recovers the semantic multilevel estimate. -/
theorem estimate_value [Field Value] [LinearOrder Value]
    (D : CountedPlannerRecursion State Context Seed Transition Value) (r : ℕ)
    (x : State) (t : MultilevelTree Seed r) : (D.estimate r x t).1 = multilevelEstimate D.toRecursion r x t := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [estimate, multilevelEstimate]
    | @node d base transition upper lower =>
      by_cases hx : (D.prepare x).1.empty = true
      · simp [estimate, multilevelEstimate, toRecursion, hx]
      · simp only [estimate, multilevelEstimate, toRecursion, hx, Bool.false_eq_true, ↓reduceIte,
          countedMultilevelAverage_value, countedFiniteSum_value]
        apply congrArg clipFive
        congr 1
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [ih (l.val + 1) (by have := l.isLt; omega), ih l.val (by have := l.isLt; omega)]
        simp only [toRecursion]

/-- A hard callback bound transfers to the actual recursive program,
including both children of every paired summand and all arithmetic loops. -/
theorem estimate_work [Field Value] [LinearOrder Value]
    (D : CountedPlannerRecursion State Context Seed Transition Value)
    (Valid : State → Prop) (B : ℕ) (hB : 1 ≤ B)
    (hPrepare : ∀ x, Valid x → (D.prepare x).2 ≤ B)
    (hSample : ∀ x, Valid x → ∀ s, (D.sample (D.prepare x).1.context s).2 ≤ B)
    (hChild : ∀ x, Valid x → ∀ s,
      let q := (D.prepare x).1.context
      let child := D.child q (D.sample q s).1
      child.2 ≤ B ∧ Valid child.1)
    (hPayoff : ∀ x, Valid x → ∀ s a,
      let q := (D.prepare x).1.context
      (D.payoff q (D.sample q s).1 a).2 ≤ B)
    (r : ℕ) (x : State) (hx : Valid x) (t : MultilevelTree Seed r) :
    (D.estimate r x t).2 ≤ 100 * B * multilevelTreeWork r t := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero =>
      simp only [estimate, multilevelTreeWork, Nat.mul_one]
      omega
    | @node d base transition upper lower =>
      have hPrep := hPrepare x hx
      rw [estimate]
      dsimp only
      by_cases hEmpty : (D.prepare x).1.empty = true
      · rw [if_pos hEmpty]
        have hPos : 1 ≤ multilevelTreeWork (d + 1) (.node base transition upper lower) := by
          rw [multilevelTreeWork]
          exact (Nat.le_add_right 1 (4 ^ (d + 1))).trans (Nat.le_add_right _ _)
        calc
          _ ≤ 100 * B := by dsimp only; omega
          _ ≤ _ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (100 * B) hPos
      · rw [if_neg hEmpty]
        let q := (D.prepare x).1.context
        let baseTerm (j : Fin (4 ^ (d + 1))) : Value × ℕ :=
          let y := D.sample q (base j)
          let pay := D.payoff q y.1 0
          (pay.1, y.2 + pay.2 + 1)
        let pairTerm (l : Fin d) (j : Fin (4 ^ (d - l.val))) : Value × ℕ :=
          let y := D.sample q (transition l j)
          let child := D.child q y.1
          let plus := D.estimate (l.val + 1) child.1 (upper l j)
          let minus := D.estimate l.val child.1 (lower l j)
          let payPlus := D.payoff q y.1 plus.1
          let payMinus := D.payoff q y.1 minus.1
          (payPlus.1 - payMinus.1, y.2 + child.2 + plus.2 + minus.2 + payPlus.2 + payMinus.2 + 3)
        let pairGroup (l : Fin d) := countedMultilevelAverage (d - l.val) (pairTerm l)
        let units (l : Fin d) (j : Fin (4 ^ (d - l.val))) : ℕ :=
          1 + multilevelTreeWork (l.val + 1) (upper l j) + multilevelTreeWork l.val (lower l j)
        have hBase : (countedMultilevelAverage (d + 1) baseTerm).2 ≤ 100 * B * 4 ^ (d + 1) := by
          have hTerm (j : Fin (4 ^ (d + 1))) : (baseTerm j).2 ≤ 0 + (2 * B + 1) := by
            have hs := hSample x hx (base j)
            have hp := hPayoff x hx (base j) 0
            dsimp only [baseTerm, q] at *
            omega
          have hb := countedMultilevelAverage_work_le (d + 1) baseTerm (fun _ => 0) (2 * B + 1) hTerm
          simp only [Finset.sum_const_zero, zero_add] at hb
          exact hb.trans (Nat.mul_le_mul_right _ (by omega))
        have hPairTerm (l : Fin d) (j : Fin (4 ^ (d - l.val))) :
            (pairTerm l j).2 ≤ (100 * B) *
              (multilevelTreeWork (l.val + 1) (upper l j) + multilevelTreeWork l.val (lower l j)) +
              (4 * B + 3) := by
          let y := D.sample q (transition l j)
          let child := D.child q y.1
          have hS : y.2 ≤ B := hSample x hx (transition l j)
          have hC : child.2 ≤ B ∧ Valid child.1 := hChild x hx (transition l j)
          have hPlus := ih (l.val + 1) (by have := l.isLt; omega) child.1 hC.2 (upper l j)
          have hMinus := ih l.val (by have := l.isLt; omega) child.1 hC.2 (lower l j)
          have hP := hPayoff x hx (transition l j) (D.estimate (l.val + 1) child.1 (upper l j)).1
          have hM := hPayoff x hx (transition l j) (D.estimate l.val child.1 (lower l j)).1
          change y.2 + child.2 + (D.estimate (l.val + 1) child.1 (upper l j)).2 +
            (D.estimate l.val child.1 (lower l j)).2 +
            (D.payoff q y.1 (D.estimate (l.val + 1) child.1 (upper l j)).1).2 +
            (D.payoff q y.1 (D.estimate l.val child.1 (lower l j)).1).2 + 3 ≤ _
          simp only [Nat.mul_add]
          dsimp only [q, y, child] at *
          omega
        have hGroup (l : Fin d) : (pairGroup l).2 + 8 ≤ 100 * B * ∑ j, units l j := by
          let g (j : Fin (4 ^ (d - l.val))) := (100 * B) *
            (multilevelTreeWork (l.val + 1) (upper l j) + multilevelTreeWork l.val (lower l j))
          have hAvg := countedMultilevelAverage_work_le (d - l.val) (pairTerm l) g
            (4 * B + 3) (hPairTerm l)
          have hN : 1 ≤ 4 ^ (d - l.val) := (Nat.le_add_left 1 _).trans (level_add_one_le_four_power _)
          calc
            (pairGroup l).2 + 8 ≤ (∑ j, g j) + (4 * B + 3 + 20) * 4 ^ (d - l.val) + 8 :=
              Nat.add_le_add_right hAvg 8
            _ ≤ (∑ j, g j) + (4 * B + 31) * 4 ^ (d - l.val) := by
              simp only [Nat.add_mul]
              omega
            _ ≤ (∑ j, g j) + (100 * B) * 4 ^ (d - l.val) :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
            _ = _ := by
              rw [Finset.mul_sum]
              simp only [g, units, Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib,
                Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
              ring
        have hPairs : (countedFiniteSum pairGroup).2 ≤ (100 * B) * (∑ l, ∑ j, units l j) + 1 := by
          rw [countedFiniteSum_work]
          calc
            _ = (∑ l, ((pairGroup l).2 + 8)) + 1 := by
              simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
              omega
            _ ≤ (∑ l, 100 * B * ∑ j, units l j) + 1 :=
              Nat.add_le_add_right (Finset.sum_le_sum (fun l _ => hGroup l)) 1
            _ = _ := by rw [Finset.mul_sum]
        change (D.prepare x).2 + (countedMultilevelAverage (d + 1) baseTerm).2 +
          (countedFiniteSum pairGroup).2 + 16 ≤ _
        rw [multilevelTreeWork]
        change _ ≤ (100 * B) * (1 + 4 ^ (d + 1) + ∑ l, ∑ j, units l j)
        simp only [Nat.mul_add, Nat.mul_one]
        omega

end CountedPlannerRecursion
/-- Changing the state representation preserves the estimate when it
preserves the actual callbacks on all reached states. -/
theorem multilevelEstimate_transport [Field Value] [LinearOrder Value]
    {State State' Seed Output Output' : Type*}
    (D : MultilevelRecursion State Seed Output Value)
    (E : MultilevelRecursion State' Seed Output' Value)
    (view : State → State') (Valid : State → Prop)
    (hFlag : ∀ x, Valid x → D.isEmpty x = E.isEmpty (view x))
    (hEmpty : ∀ x, Valid x → D.emptyValue x = E.emptyValue (view x))
    (hOffset : ∀ x, Valid x → D.offset x = E.offset (view x))
    (hCoefficient : ∀ x, Valid x → D.coefficient x = E.coefficient (view x))
    (hChild : ∀ x, Valid x → ∀ s,
      view (D.child x (D.sample x s)) = E.child (view x) (E.sample (view x) s))
    (hValid : ∀ x, Valid x → ∀ s, Valid (D.child x (D.sample x s)))
    (hPayoff : ∀ x, Valid x → ∀ s a,
      D.payoff x (D.sample x s) a = E.payoff (view x) (E.sample (view x) s) a)
    (r : ℕ) (x : State) (hx : Valid x) (t : MultilevelTree Seed r) :
    multilevelEstimate D r x t = multilevelEstimate E r (view x) t := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [multilevelEstimate]
    | @node d base transition upper lower =>
      by_cases he : D.isEmpty x = true
      · have he' : E.isEmpty (view x) = true := (hFlag x hx).symm.trans he
        simp only [multilevelEstimate, he, he', if_true, hEmpty x hx]
      · have he' : ¬ E.isEmpty (view x) = true := fun h => he ((hFlag x hx).trans h)
        simp only [multilevelEstimate, if_neg he, if_neg he', hOffset x hx, hCoefficient x hx, hPayoff x hx]
        apply congrArg clipFive
        congr 1
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        let s := transition l j
        let c := D.child x (D.sample x s)
        have hc : Valid c := hValid x hx s
        have hup := ih (l.val + 1) (by have := l.isLt; omega) c hc (upper l j)
        have hlo := ih l.val (by have := l.isLt; omega) c hc (lower l j)
        rw [hup, hlo, hChild x hx s]

end ProphetSecretary.Statistics
