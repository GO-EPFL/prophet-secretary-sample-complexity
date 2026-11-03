import ProphetSecretary.Analysis.MultilevelWork
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite trees for multilevel scalar estimates

Each paired summand samples one transition. Both recursive copies use its
child state, while their random subtrees are separate fields. This is the
coupling in the estimator of `thm:scalar-planner`.
-/

open scoped BigOperators

namespace ProphetSecretary.Analysis

/-- The finite random data used by a level-indexed multilevel call. -/
inductive MultilevelTree (Seed : Type*) : ℕ → Type _
  | zero : MultilevelTree Seed 0
  | node {r : ℕ}
      (base : Fin (4 ^ (r + 1)) → Seed)
      (transition : (l : Fin r) → Fin (4 ^ (r - l.val)) → Seed)
      (upper : (l : Fin r) → Fin (4 ^ (r - l.val)) → MultilevelTree Seed (l.val + 1))
      (lower : (l : Fin r) → Fin (4 ^ (r - l.val)) → MultilevelTree Seed l.val) :
      MultilevelTree Seed (r + 1)

/-- Computational data for the weighted scalar recursion. Regularity and
distributional properties are separate mathematical obligations. -/
structure MultilevelRecursion (State Seed Transition Value : Type*) where
  isEmpty : State → Bool
  emptyValue : State → Value
  offset : State → Value
  coefficient : State → Value
  sample : State → Seed → Transition
  child : State → Transition → State
  payoff : State → Transition → Value → Value

variable {Value : Type*} [Field Value] [LinearOrder Value]

/-- Projection onto the known range of weighted continuation values. -/
def clipFive (x : Value) : Value := max 0 (min 5 x)

lemma clipFive_nonnegative (x : Value) : 0 ≤ clipFive x := le_max_left _ _

lemma clipFive_le_five [IsStrictOrderedRing Value] (x : Value) : clipFive x ≤ 5 := by
  exact max_le (by norm_num) (min_le_left _ _)

lemma clipFive_eq_self {x : Value} (hx0 : 0 ≤ x) (hx5 : x ≤ 5) : clipFive x = x := by
  simp [clipFive, min_eq_right hx5, max_eq_right hx0]

lemma clipFive_abs_sub_le [IsStrictOrderedRing Value] (x : Value) {v : Value} (hv0 : 0 ≤ v) (hv5 : v ≤ 5) :
    |clipFive x - v| ≤ |x - v| := by
  by_cases hx0 : 0 ≤ x
  · by_cases hx5 : x ≤ 5
    · rw [clipFive_eq_self hx0 hx5]
    · have hx : 5 ≤ x := le_of_not_ge hx5
      have hvx : v ≤ x := hv5.trans hx
      have hclip : clipFive x = 5 := by simp [clipFive, min_eq_left hx]
      rw [hclip, abs_of_nonneg (sub_nonneg.mpr hv5),
        abs_of_nonneg (sub_nonneg.mpr hvx)]
      linarith
  · have hx : x ≤ 0 := le_of_not_ge hx0
    have hclip : clipFive x = 0 := by
      unfold clipFive
      rw [min_eq_right (hx.trans (by norm_num : (0 : Value) ≤ 5)), max_eq_left hx]
    have hxv : x ≤ v := hx.trans hv0
    rw [hclip, abs_of_nonpos (sub_nonpos.mpr hv0),
      abs_of_nonpos (sub_nonpos.mpr hxv)]
    linarith

lemma clipFive_sq_error_le [IsStrictOrderedRing Value] (x : Value) {v : Value}
    (hv0 : 0 ≤ v) (hv5 : v ≤ 5) : (clipFive x - v) ^ 2 ≤ (x - v) ^ 2 := by
  have h := clipFive_abs_sub_le x hv0 hv5
  have hp := mul_nonneg (sub_nonneg.mpr h)
    (add_nonneg (abs_nonneg (x - v)) (abs_nonneg (clipFive x - v)))
  nlinarith [sq_abs (clipFive x - v), sq_abs (x - v)]

/-- The deterministic evaluation of the multilevel estimator from its finite
random tree. Level zero returns zero, even at an empty state. -/
def multilevelEstimate {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition Value) :
    (r : ℕ) → State → MultilevelTree Seed r → Value
  | 0, _, .zero => 0
  | r + 1, x, .node base transition upper lower =>
      if D.isEmpty x then D.emptyValue x else
      clipFive (D.offset x + D.coefficient x *
        ((1 / ((4 : Value) ^ (r + 1))) *
            ∑ j : Fin (4 ^ (r + 1)), D.payoff x (D.sample x (base j)) 0 +
          ∑ l : Fin r, (1 / ((4 : Value) ^ (r - l.val))) *
            ∑ j : Fin (4 ^ (r - l.val)),
              let y := D.sample x (transition l j)
              let child := D.child x y
              D.payoff x y (multilevelEstimate D (l.val + 1) child (upper l j)) -
                D.payoff x y (multilevelEstimate D l.val child (lower l j))))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

lemma multilevelEstimate_zero {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition Value) (x : State)
    (t : MultilevelTree Seed 0) : multilevelEstimate D 0 x t = 0 := by
  cases t
  simp [multilevelEstimate]

lemma multilevelEstimate_empty {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition Value) (r : ℕ) (x : State)
    (hx : D.isEmpty x = true) (t : MultilevelTree Seed (r + 1)) :
    multilevelEstimate D (r + 1) x t = D.emptyValue x := by
  cases t
  simp [multilevelEstimate, hx]

lemma multilevelEstimate_bounds [IsStrictOrderedRing Value] {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition Value)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) :
    0 ≤ multilevelEstimate D r x t ∧ multilevelEstimate D r x t ≤ 5 := by
  cases t with
  | zero => simp [multilevelEstimate]
  | node base transition upper lower =>
    by_cases hx : D.isEmpty x = true
    · simpa [multilevelEstimate, hx] using hEmpty x hx
    · simp only [multilevelEstimate, hx, Bool.false_eq_true, ↓reduceIte]
      exact ⟨clipFive_nonnegative _, clipFive_le_five _⟩

/-- Number of transition/payoff units and recursive-call nodes in the full
tree. Early returns at empty states can only reduce this count. -/
def multilevelTreeWork {Seed : Type*} : (r : ℕ) → MultilevelTree Seed r → ℕ
  | 0, .zero => 1
  | r + 1, .node _ _ upper lower =>
      1 + 4 ^ (r + 1) +
        ∑ l : Fin r, ∑ j : Fin (4 ^ (r - l.val)),
          (1 + multilevelTreeWork (l.val + 1) (upper l j) +
            multilevelTreeWork l.val (lower l j))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

/-- A deterministic level envelope, counting both copies in every pair. -/
def multilevelWorkEnvelope : ℕ → ℕ
  | 0 => 1
  | r + 1 => 1 + ∑ l : Fin (r + 1), 4 ^ (r + 1 - l.val) *
      (1 + multilevelWorkEnvelope l.val +
        if l.val = 0 then 0 else multilevelWorkEnvelope (l.val - 1))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

lemma multilevelWorkEnvelope_zero : multilevelWorkEnvelope 0 = 1 := by
  simp [multilevelWorkEnvelope]

lemma multilevelTreeWork_le_envelope {Seed : Type*} (r : ℕ)
    (t : MultilevelTree Seed r) : multilevelTreeWork r t ≤ multilevelWorkEnvelope r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases t with
    | zero => simp [multilevelTreeWork, multilevelWorkEnvelope]
    | @node n base transition upper lower =>
      rw [multilevelTreeWork, multilevelWorkEnvelope, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, multilevelWorkEnvelope_zero,
        ite_true, Nat.add_zero, Nat.reduceAdd, Fin.val_succ, Nat.add_sub_add_right,
        Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      have hsum :
          (∑ l : Fin n, ∑ j : Fin (4 ^ (n - l.val)),
            (1 + multilevelTreeWork (l.val + 1) (upper l j) +
              multilevelTreeWork l.val (lower l j))) ≤
            ∑ l : Fin n, 4 ^ (n - l.val) *
              (1 + multilevelWorkEnvelope (l.val + 1) + multilevelWorkEnvelope l.val) := by
        apply Finset.sum_le_sum
        intro l _
        calc
          _ ≤ ∑ _j : Fin (4 ^ (n - l.val)),
              (1 + multilevelWorkEnvelope (l.val + 1) + multilevelWorkEnvelope l.val) := by
            apply Finset.sum_le_sum
            intro j _
            have hu := ih (l.val + 1) (by have := l.isLt; omega) (upper l j)
            have hl := ih l.val (by have := l.isLt; omega) (lower l j)
            omega
          _ = _ := by simp
      omega

/-- The full tree has a hard geometric size bound, for every realization of
its seeds. This counts units; their arithmetic/bit cost is supplied by the
transition and payoff implementations. -/
theorem multilevelTreeWork_le {Seed : Type*} (r : ℕ) (t : MultilevelTree Seed r) :
    (multilevelTreeWork r t : ℝ) ≤ 4 * (16 : ℝ) ^ r := by
  have hbound := multilevel_work_bound (fun n => (multilevelWorkEnvelope n : ℝ)) 1
    (by norm_num) (by simp [multilevelWorkEnvelope_zero])
    (by
      intro n
      rw [multilevelWorkEnvelope]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_ite, Nat.cast_zero]
      unfold geometricConvolution
      rw [Finset.sum_range]) r
  have htree := multilevelTreeWork_le_envelope r t
  have htreeR : (multilevelTreeWork r t : ℝ) ≤ (multilevelWorkEnvelope r : ℝ) := by
    exact_mod_cast htree
  simpa using htreeR.trans hbound

end ProphetSecretary.Analysis
