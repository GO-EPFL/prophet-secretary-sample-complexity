import ProphetSecretary.Statistics.ScalarPlannerBitTree
import ProphetSecretary.Analysis.CanonicalExpression

/-!
# The multilevel loop with an executed bit counter

Each numerical block stores its inputs once, runs the binary arithmetic,
and returns its measured cost. A pair still shares its transition and
child state. The same driver applies to the binary empirical callbacks.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

private lemma canonicalVectorGet_ofFn {α : Type*} {K : ℕ} (f : Fin K → α) (i : Fin K) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

def countedCanonicalArraySum {K : ℕ} (f : Fin K → BinaryRational × ℕ) : BinaryRational × ℕ :=
  let a := Vector.ofFn f
  let q := countedCanonicalEval (fun i => (a.get i).1)
    (sumList (List.finRange K) ArithmeticExpression.input)
  (q.1,q.2+(∑ i : Fin K,(a.get i).2)+8*K+4)

def countedCanonicalAverage (d : ℕ) (f : Fin (4^d) → BinaryRational × ℕ) : BinaryRational × ℕ :=
  let a := Vector.ofFn f
  let q := countedCanonicalEval (fun i => (a.get i).1) (multilevelAverageExpression d)
  (q.1,q.2+(∑ i : Fin (4^d),(a.get i).2)+8*4^d+4)

def countedCanonicalUpdate (o c b p : BinaryRational) : BinaryRational × ℕ :=
  let q := countedCanonicalEval (![o,c,b,p]) multilevelUpdateExpression
  (q.1,q.2+3)

lemma countedCanonicalArraySum_value {K : ℕ} (f : Fin K → BinaryRational × ℕ) :
    (countedCanonicalArraySum f).1=∑ i, (f i).1 := by
  simp only [countedCanonicalArraySum,canonicalVectorGet_ofFn,countedCanonicalEval_value,eval_sumList,eval]
  rw [← List.ofFn_eq_map,List.sum_ofFn]

lemma countedCanonicalAverage_value (d : ℕ) (f : Fin (4^d) → BinaryRational × ℕ) :
    (countedCanonicalAverage d f).1=(1/(4:BinaryRational)^d)*∑ i, (f i).1 := by
  simp only [countedCanonicalAverage,canonicalVectorGet_ofFn,countedCanonicalEval_value,
    multilevelAverageExpression,eval,Int.cast_one,Int.cast_pow,Int.cast_ofNat,eval_sumList]
  congr 1

lemma countedCanonicalUpdate_value (o c b p : BinaryRational) :
    (countedCanonicalUpdate o c b p).1=clipFive (o+c*(b+p)) := by
  simp only [countedCanonicalUpdate,countedCanonicalEval_value,multilevelUpdateExpression,
    eval,Int.cast_zero,Int.cast_ofNat]
  rfl

namespace CountedPlannerRecursion

variable {State Context Seed Transition : Type*}

def canonicalEstimate (D : CountedPlannerRecursion State Context Seed Transition BinaryRational) :
    (r : ℕ) → State → MultilevelTree Seed r → BinaryRational × ℕ
  | 0, _, .zero => (0,1)
  | r+1, x, .node base tr up lo =>
      let q := D.prepare x
      if q.1.empty then (q.1.emptyValue,q.2+2) else
      let b := countedCanonicalAverage (r+1) (fun j =>
        let y := D.sample q.1.context (base j)
        let a := D.payoff q.1.context y.1 0
        (a.1,y.2+a.2+2))
      let p := countedCanonicalArraySum (fun l : Fin r =>
        countedCanonicalAverage (r-l.val) (fun j =>
          let y := D.sample q.1.context (tr l j)
          let u := D.child q.1.context y.1
          let a := canonicalEstimate D (l.val+1) u.1 (up l j)
          let b := canonicalEstimate D l.val u.1 (lo l j)
          let ap := D.payoff q.1.context y.1 a.1
          let bp := D.payoff q.1.context y.1 b.1
          let s := BinaryRational.countedOperation .sub ap.1 bp.1
          (s.1,y.2+u.2+a.2+b.2+ap.2+bp.2+s.2+6)))
      let v := countedCanonicalUpdate q.1.offset q.1.coefficient b.1 p.1
      (v.1,q.2+b.2+p.2+v.2+4)
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

theorem canonicalEstimate_value (D : CountedPlannerRecursion State Context Seed Transition BinaryRational)
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) :
    (D.canonicalEstimate r x t).1=(D.estimate r x t).1 := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [canonicalEstimate,estimate]
    | @node d base tr up lo =>
      have hu (l : Fin d) (x' : State) (t' : MultilevelTree Seed (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) x' t'
      have hl (l : Fin d) (x' : State) (t' : MultilevelTree Seed l.val) :=
        ih l.val (by have := l.isLt; omega) x' t'
      by_cases he : (D.prepare x).1.empty=true
      · simp only [canonicalEstimate,estimate,he,if_true]
      · simp only [canonicalEstimate,estimate,if_neg he,countedCanonicalArraySum_value,countedCanonicalAverage_value,
          countedCanonicalUpdate_value,countedMultilevelAverage_value,countedFiniteSum_value,
          BinaryRational.countedOperation_value,BinaryRational.applyOperation,hu,hl]

end CountedPlannerRecursion

end ProphetSecretary.Statistics
