import ProphetSecretary.Statistics.PlannerNumericBits
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Binary evaluation of the multilevel tree

The numeric loop stores each callback result once. Its averaging, paired
differences, and clipping are evaluated by the binary fraction operations.
The callback equations specify the local operations to be substituted in
this driver.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

private lemma binaryVectorGet_ofFn {α : Type*} {K : ℕ} (f : Fin K → α) (i : Fin K) :
    (Vector.ofFn f).get i = f i := by simp [Vector.get]

def countedBinaryArraySum {K : ℕ} (f : Fin K → BinaryFraction × ℕ) : BinaryFraction × ℕ :=
  let a := Vector.ofFn f
  let q := countedBinaryEval (fun i => (a.get i).1)
    (sumList (List.finRange K) ArithmeticExpression.input)
  (q.1,q.2+(∑ i : Fin K, (a.get i).2)+8*K+1)

lemma countedBinaryArraySum_value {K : ℕ} (f : Fin K → BinaryFraction × ℕ)
    (hf : ∀ i, 0 < binaryWordValue (f i).1.denominator) :
    (countedBinaryArraySum f).1.value = ∑ i, (f i).1.value ∧
      0 < binaryWordValue (countedBinaryArraySum f).1.denominator := by
  have h := countedBinaryEval_semantics (fun i => (f i).1) hf
    (sumList (List.finRange K) ArithmeticExpression.input)
  simp only [eval_sumList,eval] at h
  have he : ((List.finRange K).map (fun i => (f i).1.value)).sum = ∑ i, (f i).1.value := by
    rw [← List.ofFn_eq_map,List.sum_ofFn]
  simpa only [countedBinaryArraySum,binaryVectorGet_ofFn,he] using h

lemma countedBinaryArraySum_work {K : ℕ} (f : Fin K → BinaryFraction × ℕ) (B : ℕ)
    (hf : ∀ i, 0 < binaryWordValue (f i).1.denominator ∧
      (f i).1.width ≤ B+1 ∧ RationalHeight (f i).1.value B) :
    (countedBinaryArraySum f).2 ≤ (∑ i, (f i).2)+8*K+1+
      (2*K+1)*(3500*((B+1)*(2*K+1)+2)^3) := by
  let e := sumList (List.finRange K) ArithmeticExpression.input
  have he : LiteralsBounded B e := literalsBounded_sumList _ _ _ (fun _ _ => trivial)
  have hw : e.work ≤ 2*K+1 := by
    have h := work_sumList_le (List.finRange K) ArithmeticExpression.input 1 (fun _ _ => le_rfl)
    simpa only [e,List.length_finRange,Nat.mul_comm,Nat.add_comm] using h
  have h := binaryExpression_work_le (fun i => (f i).1) B (2*K+1) hf e he hw
  simp only [countedBinaryArraySum,binaryVectorGet_ofFn]
  change (countedBinaryEval (fun i => (f i).1) e).2+_+8*K+1 ≤ _
  omega

def countedBinaryArrayAverage (d : ℕ) (f : Fin (4^d) → BinaryFraction × ℕ) : BinaryFraction × ℕ :=
  let a := Vector.ofFn f
  let q := countedBinaryEval (fun i => (a.get i).1) (multilevelAverageExpression d)
  (q.1,q.2+(∑ i : Fin (4^d), (a.get i).2)+8*4^d+1)

lemma countedBinaryArrayAverage_value (d : ℕ) (f : Fin (4^d) → BinaryFraction × ℕ)
    (hf : ∀ i, 0 < binaryWordValue (f i).1.denominator) :
    (countedBinaryArrayAverage d f).1.value = (1/(4:ℚ)^d)*∑ i, (f i).1.value ∧
      0 < binaryWordValue (countedBinaryArrayAverage d f).1.denominator := by
  have h := countedBinaryEval_semantics (fun i => (f i).1) hf (multilevelAverageExpression d)
  have he := multilevelAverageExpression_value d (fun i => ((f i).1.value,0))
  rw [countedMultilevelAverage_value] at he
  simpa only [countedBinaryArrayAverage,binaryVectorGet_ofFn,he] using h

lemma countedBinaryArrayAverage_work (d : ℕ) (f : Fin (4^d) → BinaryFraction × ℕ) (B : ℕ)
    (hB : 2*d ≤ B) (hf : ∀ i, 0 < binaryWordValue (f i).1.denominator ∧
      (f i).1.width ≤ B+1 ∧ RationalHeight (f i).1.value B) :
    (countedBinaryArrayAverage d f).2 ≤ (∑ i, (f i).2)+8*4^d+1+
      (2*4^d+5)*(3500*((B+1)*(2*4^d+5)+2)^3) := by
  have h := (countedMultilevelAverage_binary_correct d (fun i => (f i).1) B hB hf).2
  simp only [countedBinaryArrayAverage,binaryVectorGet_ofFn]
  omega

def countedBinaryClippedUpdate (o c b p : BinaryFraction) : BinaryFraction × ℕ :=
  countedBinaryEval (![o,c,b,p]) multilevelUpdateExpression

lemma countedBinaryClippedUpdate_value (o c b p : BinaryFraction)
    (ho : 0 < binaryWordValue o.denominator) (hc : 0 < binaryWordValue c.denominator)
    (hb : 0 < binaryWordValue b.denominator) (hp : 0 < binaryWordValue p.denominator) :
    (countedBinaryClippedUpdate o c b p).1.value = clipFive (o.value+c.value*(b.value+p.value)) ∧
      0 < binaryWordValue (countedBinaryClippedUpdate o c b p).1.denominator := by
  have h (i : Fin 4) : 0 < binaryWordValue ((![o,c,b,p] : Fin 4 → BinaryFraction) i).denominator := by
    fin_cases i <;> assumption
  have he := countedBinaryEval_semantics (![o,c,b,p]) h multilevelUpdateExpression
  exact he

namespace CountedPlannerRecursion

variable {State Context Seed Transition : Type*}

def binaryEstimate (D : CountedPlannerRecursion State Context Seed Transition BinaryFraction) :
    (r : ℕ) → State → MultilevelTree Seed r → BinaryFraction × ℕ
  | 0, _, .zero => (BinaryFraction.ofInt 0,1)
  | r+1, x, .node base tr up lo =>
      let q := D.prepare x
      if q.1.empty then (q.1.emptyValue,q.2+2) else
      let b := countedBinaryArrayAverage (r+1) (fun j =>
        let y := D.sample q.1.context (base j)
        let a := D.payoff q.1.context y.1 (BinaryFraction.ofInt 0)
        (a.1,y.2+a.2+2))
      let p := countedBinaryArraySum (fun l : Fin r =>
        countedBinaryArrayAverage (r-l.val) (fun j =>
          let y := D.sample q.1.context (tr l j)
          let u := D.child q.1.context y.1
          let a := binaryEstimate D (l.val+1) u.1 (up l j)
          let b := binaryEstimate D l.val u.1 (lo l j)
          let ap := D.payoff q.1.context y.1 a.1
          let bp := D.payoff q.1.context y.1 b.1
          let s := ap.1.countedSub bp.1
          (s.1,y.2+u.2+a.2+b.2+ap.2+bp.2+s.2+6)))
      let v := countedBinaryClippedUpdate q.1.offset q.1.coefficient b.1 p.1
      (v.1,q.2+b.2+p.2+v.2+4)
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

/-- The binary driver realizes the same arithmetic recursion when each
local callback realizes its declared operation. -/
theorem binaryEstimate_value
    (D : CountedPlannerRecursion State Context Seed Transition BinaryFraction)
    (Q : CountedPlannerRecursion State Context Seed Transition ℚ)
    (hP : ∀ x,
      let a := (D.prepare x).1
      let b := (Q.prepare x).1
      a.context = b.context ∧ a.empty = b.empty ∧
        (a.emptyValue.value = b.emptyValue ∧ 0 < binaryWordValue a.emptyValue.denominator) ∧
        (a.offset.value = b.offset ∧ 0 < binaryWordValue a.offset.denominator) ∧
        a.coefficient.value = b.coefficient ∧ 0 < binaryWordValue a.coefficient.denominator)
    (hS : ∀ c s, (D.sample c s).1 = (Q.sample c s).1)
    (hC : ∀ c o, (D.child c o).1 = (Q.child c o).1)
    (hF : ∀ c o a, 0 < binaryWordValue a.denominator →
      (D.payoff c o a).1.value = (Q.payoff c o a.value).1 ∧
        0 < binaryWordValue (D.payoff c o a).1.denominator)
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) :
    (D.binaryEstimate r x t).1.value = (Q.estimate r x t).1 ∧
      0 < binaryWordValue (D.binaryEstimate r x t).1.denominator := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero =>
      rw [binaryEstimate,estimate]
      exact ⟨BinaryFraction.ofInt_value 0,(show 0 < binaryWordValue [true] by decide)⟩
    | @node d base tr up lo =>
      let a := (D.prepare x).1
      let q := (Q.prepare x).1
      have hp := hP x
      have hc : a.context = q.context := hp.1
      have he : a.empty = q.empty := hp.2.1
      by_cases ha : a.empty = true
      · have hq : q.empty = true := he ▸ ha
        rw [binaryEstimate,estimate]
        change (if a.empty then _ else _ : BinaryFraction × ℕ).1.value =
          (if q.empty then _ else _ : ℚ × ℕ).1 ∧
          0 < binaryWordValue (if a.empty then _ else _ : BinaryFraction × ℕ).1.denominator
        rw [if_pos ha,if_pos hq]
        exact hp.2.2.1
      · have hq : ¬q.empty = true := fun h => ha (he.trans h)
        let f := fun j : Fin (4^(d+1)) =>
          let y := D.sample a.context (base j)
          let z := D.payoff a.context y.1 (BinaryFraction.ofInt 0)
          (z.1,y.2+z.2+2)
        let g := fun (l : Fin d) (j : Fin (4^(d-l.val))) =>
          let y := D.sample a.context (tr l j)
          let u := D.child a.context y.1
          let v := D.binaryEstimate (l.val+1) u.1 (up l j)
          let w := D.binaryEstimate l.val u.1 (lo l j)
          let ap := D.payoff a.context y.1 v.1
          let bp := D.payoff a.context y.1 w.1
          let z := ap.1.countedSub bp.1
          (z.1,y.2+u.2+v.2+w.2+ap.2+bp.2+z.2+6)
        let baseAvg := countedBinaryArrayAverage (d+1) f
        let pairs := countedBinaryArraySum (fun l : Fin d => countedBinaryArrayAverage (d-l.val) (g l))
        have hF0 (j : Fin (4^(d+1))) : (f j).1.value =
            (Q.payoff q.context (Q.sample q.context (base j)).1 0).1 ∧
            0 < binaryWordValue (f j).1.denominator := by
          have h := hF a.context (D.sample a.context (base j)).1 (BinaryFraction.ofInt 0)
            (show 0 < binaryWordValue [true] by decide)
          simpa only [hc,hS,BinaryFraction.ofInt_value,Int.cast_zero,f] using h
        have hG (l : Fin d) (j : Fin (4^(d-l.val))) :
            let y := (Q.sample q.context (tr l j)).1
            let u := (Q.child q.context y).1
            (g l j).1.value = (Q.payoff q.context y (Q.estimate (l.val+1) u (up l j)).1).1 -
              (Q.payoff q.context y (Q.estimate l.val u (lo l j)).1).1 ∧
              0 < binaryWordValue (g l j).1.denominator := by
          let y := (D.sample a.context (tr l j)).1
          let u := (D.child a.context y).1
          let v := (D.binaryEstimate (l.val+1) u (up l j)).1
          let w := (D.binaryEstimate l.val u (lo l j)).1
          have hv := ih (l.val+1) (by have := l.isLt; omega) u (up l j)
          have hw := ih l.val (by have := l.isLt; omega) u (lo l j)
          have hV := hF a.context y v hv.2
          have hW := hF a.context y w hw.2
          have h := BinaryFraction.countedSub_correct (D.payoff a.context y v).1 (D.payoff a.context y w).1 hV.2 hW.2
          refine ⟨h.1.trans ?_,h.2⟩
          rw [hV.1,hW.1,show v.value = _ from hv.1,show w.value = _ from hw.1]
          simp only [u,y,hc,hS,hC]
        have hB := countedBinaryArrayAverage_value (d+1) f (fun j => (hF0 j).2)
        have hL (l : Fin d) := countedBinaryArrayAverage_value (d-l.val) (g l) (fun j => (hG l j).2)
        have hP' := countedBinaryArraySum_value (fun l : Fin d => countedBinaryArrayAverage (d-l.val) (g l))
          (fun l => (hL l).2)
        have hV := countedBinaryClippedUpdate_value a.offset a.coefficient baseAvg.1 pairs.1
          hp.2.2.2.1.2 hp.2.2.2.2.2 hB.2 hP'.2
        rw [binaryEstimate,estimate]
        change (if a.empty then _ else _ : BinaryFraction × ℕ).1.value =
          (if q.empty then _ else _ : ℚ × ℕ).1 ∧
          0 < binaryWordValue (if a.empty then _ else _ : BinaryFraction × ℕ).1.denominator
        rw [if_neg ha,if_neg hq]
        refine ⟨hV.1.trans ?_,hV.2⟩
        rw [hp.2.2.2.1.1,hp.2.2.2.2.1]
        simp only [countedMultilevelAverage_value,countedFiniteSum_value]
        apply congrArg clipFive
        rw [show baseAvg.1.value = _ from hB.1,show pairs.1.value = _ from hP'.1]
        simp only [fun j => (hF0 j).1,fun l => (hL l).1,fun l j => (hG l j).1,q]

end CountedPlannerRecursion

end ProphetSecretary.Statistics
