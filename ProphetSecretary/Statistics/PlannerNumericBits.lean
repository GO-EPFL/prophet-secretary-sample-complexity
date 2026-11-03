import ProphetSecretary.Analysis.ArithmeticExpressionBits
import ProphetSecretary.Statistics.ScalarPlannerWorkTree

/-!
# Bit evaluation of the planner's finite arithmetic expressions

The averages and clipped update evaluate the same arithmetic as the
recursive program after its transition and child values have been computed.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

lemma binaryExpression_work_le {ι : Type*} (x : ι → BinaryFraction) (B W : ℕ)
    (hx : ∀ i, 0 < binaryWordValue (x i).denominator ∧ (x i).width ≤ B+1 ∧ RationalHeight (x i).value B)
    (e : ArithmeticExpression ι) (he : LiteralsBounded B e) (hW : e.work ≤ W) :
    (countedBinaryEval x e).2 ≤ W*(3500*((B+1)*W+2)^3) := by
  have h := (countedBinaryEval_correct x B hx e he).2.2.2
  have hW' := Nat.add_le_add_right (Nat.mul_le_mul_left (B+1) hW) 2
  exact h.trans (Nat.mul_le_mul hW (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW' 3)))

def multilevelAverageExpression (d : ℕ) : ArithmeticExpression (Fin (4^d)) :=
  .mul (.div (.integer 1) (.integer ((4:ℤ)^d)))
    (sumList (List.finRange (4^d)) ArithmeticExpression.input)

lemma multilevelAverageExpression_value (d : ℕ) (f : Fin (4^d) → ℚ × ℕ) :
    eval (fun j => (f j).1) (multilevelAverageExpression d) = (countedMultilevelAverage d f).1 := by
  rw [countedMultilevelAverage_value]
  simp only [multilevelAverageExpression,eval,Int.cast_pow,Int.cast_ofNat,Int.cast_one,eval_sumList]
  congr 1

lemma multilevelAverageExpression_work (d : ℕ) : (multilevelAverageExpression d).work ≤ 2*4^d+5 := by
  have h := work_sumList_le (List.finRange (4^d)) ArithmeticExpression.input 1 (fun _ _ => le_rfl)
  simp only [List.length_finRange] at h
  change 3+(sumList (List.finRange (4^d)) ArithmeticExpression.input).work+1 ≤ _
  omega

theorem countedMultilevelAverage_binary_correct (d : ℕ) (x : Fin (4^d) → BinaryFraction)
    (B : ℕ) (hB : 2*d ≤ B)
    (hx : ∀ j, 0 < binaryWordValue (x j).denominator ∧ (x j).width ≤ B+1 ∧ RationalHeight (x j).value B) :
    let q := countedBinaryEval x (multilevelAverageExpression d)
    let W := 2*4^d+5
    q.1.value = (countedMultilevelAverage d (fun j => ((x j).value,0))).1 ∧
      q.2 ≤ W*(3500*((B+1)*W+2)^3) := by
  have hPow : ((4:ℤ)^d).natAbs ≤ 2^B := by
    rw [Int.natAbs_pow,show (4:ℤ).natAbs = 2^2 by decide,← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hB
  have he : LiteralsBounded B (multilevelAverageExpression d) :=
    ⟨⟨Nat.succ_le_of_lt (by positivity),hPow⟩,literalsBounded_sumList _ _ _ (fun _ _ => trivial)⟩
  refine ⟨(countedBinaryEval_correct x B hx _ he).1.trans ?_,
    binaryExpression_work_le x B _ hx _ he (multilevelAverageExpression_work d)⟩
  exact multilevelAverageExpression_value d (fun j => ((x j).value,0))

def multilevelUpdateExpression : ArithmeticExpression (Fin 4) :=
  .maximum (.integer 0) (.minimum (.integer 5)
    (.add (.input 0) (.mul (.input 1) (.add (.input 2) (.input 3)))))

theorem multilevelUpdate_binary_correct (x : Fin 4 → BinaryFraction) (B : ℕ) (hB : 3 ≤ B)
    (hx : ∀ j, 0 < binaryWordValue (x j).denominator ∧ (x j).width ≤ B+1 ∧ RationalHeight (x j).value B) :
    let q := countedBinaryEval x multilevelUpdateExpression
    q.1.value = clipFive ((x 0).value+(x 1).value*((x 2).value+(x 3).value)) ∧
      q.2 ≤ 11*(3500*((B+1)*11+2)^3) := by
  have he₀ : LiteralsBounded 3 multilevelUpdateExpression := by
    norm_num [multilevelUpdateExpression,LiteralsBounded]
  have he := he₀.mono hB
  exact ⟨(countedBinaryEval_correct x B hx _ he).1,
    binaryExpression_work_le x B _ hx _ he (by decide)⟩

end ProphetSecretary.Statistics
