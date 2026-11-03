import ProphetSecretary.Analysis.ArithmeticExpressionHeight
import ProphetSecretary.Statistics.PlannerChoiceWork

/-!
# Rational sizes in the transition sampler

Categorical prefix arithmetic is separate from the recursive estimator.
Its inputs are stored probabilities or bounded counts, so every intermediate
in the actual comparison expressions has polynomial height.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

variable {n : ℕ}

lemma plannerProbabilityExpression_literals (i : Fin n) : LiteralsBounded 2 (plannerProbabilityExpression i) := by
  norm_num [plannerProbabilityExpression,LiteralsBounded]

lemma plannerFailureExpression_literals (i : Fin n) : LiteralsBounded 2 (plannerFailureExpression i) := by
  exact ⟨by norm_num [LiteralsBounded],plannerProbabilityExpression_literals i⟩

lemma plannerFirstWeightExpression_literals (l : List (Fin n)) (i : Fin n) :
    LiteralsBounded 2 (plannerFirstWeightExpression l i) :=
  ⟨⟨plannerProbabilityExpression_literals i,literalsBounded_productList _ _ _ (fun j _ => plannerFailureExpression_literals j)⟩,
    ⟨by norm_num [LiteralsBounded],literalsBounded_productList _ _ _ (fun j _ => plannerFailureExpression_literals j)⟩⟩

lemma plannerFirstPrefixExpression_literals (l : List (Fin n)) (i : Fin n) :
    LiteralsBounded 2 (plannerFirstPrefixExpression l i) :=
  literalsBounded_sumList _ _ _ (fun j _ => plannerFirstWeightExpression_literals l j)

theorem countedPlannerFirstPrefix_intermediate_height (l : List (Fin n)) (i : Fin n)
    (p : Fin n → ℚ) (P : ℕ) (hp : ∀ j, RationalHeight (p j) P)
    (q : ℚ) (hq : q ∈ evalValues p (countedPlannerFirstPrefix l i).1) :
    RationalHeight q ((P+3)*(1+l.length*(16+24*l.length))) := by
  rw [countedPlannerFirstPrefix_value] at hq
  have h := evalValues_rationalHeight p (P+2) (fun j => (hp j).mono (by omega))
    (plannerFirstPrefixExpression l i) ((plannerFirstPrefixExpression_literals l i).mono (by omega)) q hq
  exact h.mono (Nat.mul_le_mul_left _ (work_plannerFirstPrefixExpression_le l i))

theorem countedPlannerUniformPrefix_intermediate_height (l : List (Fin n)) (i : Fin n)
    (B : ℕ) (hB : l.length ≤ 2^B) (q : ℚ)
    (hq : q ∈ evalValues (fun _ => (0:ℚ)) (countedPlannerUniformPrefix l i).1) :
    RationalHeight q ((B+1)*(1+4*l.length)) := by
  have hL : LiteralsBounded B (countedPlannerUniformPrefix l i).1 := by
    rw [countedPlannerUniformPrefix_value]
    apply literalsBounded_sumList
    intro j _
    refine ⟨Nat.succ_le_of_lt (by positivity),?_⟩
    exact hB
  exact (evalValues_rationalHeight _ B (fun _ => rationalHeight_zero.mono (Nat.zero_le _)) _ hL q hq).mono
    (Nat.mul_le_mul_left _ (countedPlannerUniformPrefix_expression_work l i))

theorem plannerBernoulli_intermediate_height (i : Fin n) (p : Fin n → ℚ) (P : ℕ)
    (hp : ∀ j, RationalHeight (p j) P) (q : ℚ) (hq : q ∈ evalValues p (plannerProbabilityExpression i)) :
    RationalHeight q (9*(P+3)) := by
  have h := evalValues_rationalHeight p (P+2) (fun j => (hp j).mono (by omega))
    (plannerProbabilityExpression i) ((plannerProbabilityExpression_literals i).mono (by omega)) q hq
  simpa only [work_plannerProbabilityExpression,Nat.mul_comm] using h

end ProphetSecretary.Statistics
