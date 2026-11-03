import ProphetSecretary.Statistics.PlannerSamplerWork

/-!
# Rational implementation of the planner transition

The rational transition makes the same comparisons and arithmetic
decisions as the real transition, on the same embedded inputs.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

variable {n : ℕ}

def plannerFieldSeedRatCast (s : PlannerFieldSeed n ℚ) : PlannerFieldSeed n ℝ :=
  ((s.1.1, fun i => s.1.2 i), (s.2.1, (fun i => s.2.2.1 i, fun i => s.2.2.2 i)))

def plannerListOutputRatCast (x : PlannerListOutput n ℚ) : PlannerListOutput n ℝ :=
  (x.1, x.2.1, x.2.2)

private lemma generatedMinimum_ratCast {α ι : Type*} [LinearOrder α]
    (l : List α) (g : α → ArithmeticExpression ι × ℕ)
    (x : ι → ℚ) (u : ℚ) (a : α) :
    arithmeticGeneratedMinimumScan l g (fun i => (x i : ℝ)) (u : ℝ) a =
      arithmeticGeneratedMinimumScan l g x u a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hh : (u : ℝ) < eval (fun j => (x j : ℝ)) (g i).1 ↔ u < eval x (g i).1 := by
      rw [← eval_ratCast, Rat.cast_lt]
    simp only [arithmeticGeneratedMinimumScan, ih, hh]

lemma countedPlannerFirstChoice_ratCast (l : List (Fin n)) (a : Fin n)
    (p : Fin n → ℚ) (u : ℚ) :
    countedPlannerFirstChoice l a (fun i => (p i : ℝ)) (u : ℝ) =
      countedPlannerFirstChoice l a p u :=
  generatedMinimum_ratCast l (countedPlannerFirstPrefix l) p u a

lemma countedPlannerUniformIdentity_ratCast (l : List (Fin n)) (a : Fin n) (u : ℚ) :
    countedPlannerUniformIdentity l a (u : ℝ) = countedPlannerUniformIdentity l a u := by
  simpa only [countedPlannerUniformIdentity, Rat.cast_zero] using
    generatedMinimum_ratCast l (countedPlannerUniformPrefix l) (fun _ : Fin n => 0) u a

lemma countedPlannerFirstCoins_ratCast (l : List (Fin n)) (p : Fin n → ℚ)
    (k : Fin n) (u : Fin n → ℚ) :
    countedPlannerFirstCoins l (fun i => (p i : ℝ)) k (fun i => (u i : ℝ)) =
      countedPlannerFirstCoins l p k u := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hh : (u i : ℝ) ≤ eval (fun j => (p j : ℝ)) (plannerProbabilityExpression i) ↔
        u i ≤ eval p (plannerProbabilityExpression i) := by
      rw [← eval_ratCast, Rat.cast_le]
    simp only [countedPlannerFirstCoins, ih, hh]

lemma countedPlannerFraction_ratCast (l : List (Fin n)) (u : Fin n → ℚ) :
    countedPlannerFraction l (fun i => (u i : ℝ)) =
      (((countedPlannerFraction l u).1 : ℝ), (countedPlannerFraction l u).2) := by
  unfold countedPlannerFraction
  rw [eval_ratCast]

lemma countedPlannerTailCoins_ratCast (l D : List (Fin n)) (s : ℚ) (u : Fin n → ℚ) :
    countedPlannerTailCoins l D (s : ℝ) (fun i => (u i : ℝ)) =
      countedPlannerTailCoins l D s u := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [countedPlannerTailCoins, ih, Rat.cast_le]

lemma countedPlannerFirstStage_ratCast (l : List (Fin n)) (a : Fin n)
    (p : Fin n → ℚ) (s : ℚ × (Fin n → ℚ)) :
    countedPlannerFirstStage l a (fun i => (p i : ℝ)) (s.1, fun i => (s.2 i : ℝ)) =
      countedPlannerFirstStage l a p s := by
  simp only [countedPlannerFirstStage, countedPlannerFirstChoice_ratCast, countedPlannerFirstCoins_ratCast]

/-- A transition preserves the selected identity, the child list, and
the operation count under the inclusion of rational values into reals. -/
theorem countedPlannerUniformSampler_ratCast (l : List (Fin n)) (p : Fin n → ℚ)
    (s : PlannerFieldSeed n ℚ) :
    countedPlannerUniformSampler l (fun i => (p i : ℝ)) (plannerFieldSeedRatCast s) =
      (plannerListOutputRatCast (countedPlannerUniformSampler l p s).1,
        (countedPlannerUniformSampler l p s).2) := by
  cases l with
  | nil => simp [countedPlannerUniformSampler, plannerListOutputRatCast]
  | cons a l =>
    simp only [countedPlannerUniformSampler, countedPlannerUniformSamplerBody, plannerFieldSeedRatCast,
      countedPlannerFirstStage_ratCast, countedPlannerUniformIdentity_ratCast,
      countedPlannerFraction_ratCast, countedPlannerTailCoins_ratCast, plannerListOutputRatCast]

end ProphetSecretary.Statistics
