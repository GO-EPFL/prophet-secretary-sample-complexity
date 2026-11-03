import ProphetSecretary.Analysis.ArithmeticScan
import ProphetSecretary.Statistics.PlannerUniformSampler

/-!
# Counted arithmetic choices of the planner sampler

Active identities are represented by a duplicate-free list. All prefix
products, cumulative sums, and comparisons are constructed by bounded list
traversals. Their arithmetic expressions have the same real values as the
probabilities used by the fixed-seed sampler.
-/

open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability
open ArithmeticExpression

variable {n : ℕ}

def plannerProbabilityExpression (i : Fin n) : ArithmeticExpression (Fin n) :=
  .div (.mul (.integer 4) (.input i)) (.add (.integer 1) (.mul (.integer 4) (.input i)))

def plannerFailureExpression (i : Fin n) : ArithmeticExpression (Fin n) :=
  .sub (.integer 1) (plannerProbabilityExpression i)

@[simp] lemma eval_plannerProbabilityExpression (p : Fin n → ℝ) (i : Fin n) :
    eval p (plannerProbabilityExpression i) = plannerBernoulliProbability (p i) := by
  simp [plannerProbabilityExpression, eval, plannerBernoulliProbability]

@[simp] lemma eval_plannerFailureExpression (p : Fin n → ℝ) (i : Fin n) :
    eval p (plannerFailureExpression i) = 1 - plannerBernoulliProbability (p i) := by
  simp [plannerFailureExpression, eval]

@[simp] lemma work_plannerProbabilityExpression (i : Fin n) : work (plannerProbabilityExpression i) = 9 := rfl
@[simp] lemma work_plannerFailureExpression (i : Fin n) : work (plannerFailureExpression i) = 11 := rfl

def plannerFirstWeightExpression (l : List (Fin n)) (i : Fin n) : ArithmeticExpression (Fin n) :=
  .div (.mul (plannerProbabilityExpression i)
    (productList (l.filter (fun j => decide (j < i))) plannerFailureExpression))
    (.sub (.integer 1) (productList l plannerFailureExpression))

def plannerFirstPrefixExpression (l : List (Fin n)) (i : Fin n) : ArithmeticExpression (Fin n) :=
  sumList (l.filter (fun j => decide (j ≤ i))) (plannerFirstWeightExpression l)

lemma eval_plannerFirstWeightExpression (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (i : Fin n) :
    eval p (plannerFirstWeightExpression l i) = plannerFirstSuccessWeight l.toFinset p i := by
  have hSet : (l.filter (fun j => decide (j < i))).toFinset = l.toFinset.filter (fun j => j < i) := by
    ext j
    simp
  simp only [plannerFirstWeightExpression, eval, eval_productList,
    eval_plannerProbabilityExpression, eval_plannerFailureExpression]
  rw [← List.prod_toFinset (fun j => 1 - plannerBernoulliProbability (p j)) (hl.filter _),
    ← List.prod_toFinset (fun j => 1 - plannerBernoulliProbability (p j)) hl, hSet]
  simp [plannerFirstSuccessWeight]

lemma eval_plannerFirstPrefixExpression (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (i : Fin n) :
    eval p (plannerFirstPrefixExpression l i) =
      categoricalPrefix l.toFinset (plannerFirstSuccessWeight l.toFinset p) i := by
  have hSet : (l.filter (fun j => decide (j ≤ i))).toFinset = l.toFinset.filter (fun j => j ≤ i) := by
    ext j
    simp
  rw [plannerFirstPrefixExpression, eval_sumList]
  simp_rw [eval_plannerFirstWeightExpression l hl p]
  rw [← List.sum_toFinset (plannerFirstSuccessWeight l.toFinset p) (hl.filter _), hSet]
  rfl

lemma work_plannerFirstWeightExpression_le (l : List (Fin n)) (i : Fin n) :
    work (plannerFirstWeightExpression l i) ≤ 15 + 24 * l.length := by
  have hPref := work_productList_le (l.filter (fun j => decide (j < i))) plannerFailureExpression 11
    (fun _ _ => le_rfl)
  have hAll := work_productList_le l plannerFailureExpression 11 (fun _ _ => le_rfl)
  have hLen := List.length_filter_le (fun j => decide (j < i)) l
  change (9 + work (productList (l.filter (fun j => decide (j < i))) plannerFailureExpression) + 1) +
    (1 + work (productList l plannerFailureExpression) + 1) + 1 ≤ _
  omega

lemma work_plannerFirstPrefixExpression_le (l : List (Fin n)) (i : Fin n) :
    work (plannerFirstPrefixExpression l i) ≤ 1 + l.length * (16 + 24 * l.length) := by
  have h := work_sumList_le (l.filter (fun j => decide (j ≤ i))) (plannerFirstWeightExpression l)
    (15 + 24 * l.length) (fun j _ => work_plannerFirstWeightExpression_le l j)
  have hLen := List.length_filter_le (fun j => decide (j ≤ i)) l
  have hCoeff : (15 + 24 * l.length) + 1 = 16 + 24 * l.length := by omega
  rw [hCoeff] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLen) 1)

def countedPlannerFirstWeight (l : List (Fin n)) (i : Fin n) : ArithmeticExpression (Fin n) × ℕ :=
  let pref :=  countedPredicateFilter (fun j => j < i) l
  let a := countedProductExpression pref.1 (fun j => (plannerFailureExpression j, 11))
  let b := countedProductExpression l (fun j => (plannerFailureExpression j, 11))
  (.div (.mul (plannerProbabilityExpression i) a.1) (.sub (.integer 1) b.1),
    pref.2 + a.2 + b.2 + 13)

lemma countedPlannerFirstWeight_value (l : List (Fin n)) (i : Fin n) :
    (countedPlannerFirstWeight l i).1 = plannerFirstWeightExpression l i := by
  simp only [countedPlannerFirstWeight, countedProductExpression_value,
    countedPredicateFilter_value, plannerFirstWeightExpression]

lemma countedPlannerFirstWeight_work (l : List (Fin n)) (i : Fin n) :
    (countedPlannerFirstWeight l i).2 ≤ 16 + 29 * l.length := by
  have hFilter := countedPredicateFilter_work (fun j => j < i) l
  have hPref := countedProductExpression_work (countedPredicateFilter (fun j => j < i) l).1
    (fun j => (plannerFailureExpression j, 11)) 11 (fun _ _ => le_rfl)
  have hAll := countedProductExpression_work l (fun j => (plannerFailureExpression j, 11)) 11
    (fun _ _ => le_rfl)
  have hLen : (countedPredicateFilter (fun j => j < i) l).1.length ≤ l.length := by
    rw [countedPredicateFilter_value]
    exact List.length_filter_le _ _
  dsimp only [countedPlannerFirstWeight]
  omega

def countedPlannerFirstPrefix (l : List (Fin n)) (i : Fin n) : ArithmeticExpression (Fin n) × ℕ :=
  let pref :=  countedPredicateFilter (fun j => j ≤ i) l
  let q := countedSumExpression pref.1 (countedPlannerFirstWeight l)
  (q.1, pref.2 + q.2)

lemma countedPlannerFirstPrefix_value (l : List (Fin n)) (i : Fin n) :
    (countedPlannerFirstPrefix l i).1 = plannerFirstPrefixExpression l i := by
  simp only [countedPlannerFirstPrefix, countedSumExpression_value,
    countedPredicateFilter_value, countedPlannerFirstWeight_value, plannerFirstPrefixExpression]

lemma countedPlannerFirstPrefix_work (l : List (Fin n)) (i : Fin n) :
    (countedPlannerFirstPrefix l i).2 ≤ 2 + 21 * l.length + 29 * l.length ^ 2 := by
  have hFilter := countedPredicateFilter_work (fun j => j ≤ i) l
  have hSum := countedSumExpression_work (countedPredicateFilter (fun j => j ≤ i) l).1
    (countedPlannerFirstWeight l) (16 + 29 * l.length)
    (fun j _ => countedPlannerFirstWeight_work l j)
  have hLen : (countedPredicateFilter (fun j => j ≤ i) l).1.length ≤ l.length := by
    rw [countedPredicateFilter_value]
    exact List.length_filter_le _ _
  have hMul := Nat.mul_le_mul_right (18 + 29 * l.length) hLen
  dsimp only [countedPlannerFirstPrefix]
  nlinarith

lemma arithmeticMinimumScan_eq_categorical {ι : Type*} (A : Finset (Fin n)) (hA : A.Nonempty)
    (l : List (Fin n)) (hList : ∀ i, i ∈ l ↔ i ∈ A) (w : Fin n → ℝ)
    (e : Fin n → ArithmeticExpression ι) (x : ι → ℝ)
    (hEval : ∀ i ∈ A, eval x (e i) = categoricalPrefix A w i) (u : ℝ) :
    (arithmeticMinimumScan l e x u (A.max' hA)).1 = categoricalUniformSample A hA w u := by
  apply le_antisymm
  · unfold categoricalUniformSample
    apply Finset.le_inf' hA
    intro i hi
    by_cases hCross : u < categoricalPrefix A w i
    · rw [if_pos hCross]
      exact arithmeticMinimumScan_le_candidate l e x u _ ((hList i).mpr hi)
        (by rwa [hEval i hi])
    · rw [if_neg hCross]
      exact arithmeticMinimumScan_le_fallback l e x u _
  · apply le_arithmeticMinimumScan l e x u _
      (categoricalUniformSample A hA w u)
      (Finset.le_max' A _ (categoricalUniformSample_mem A hA w u))
    intro i hi hCross
    have hiA := (hList i).mp hi
    rw [hEval i hiA] at hCross
    have h := Finset.inf'_le (fun j => if u < categoricalPrefix A w j then j else A.max' hA) hiA
    simpa only [categoricalUniformSample, if_pos hCross] using h

def countedPlannerFirstChoice {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (fallback : Fin n) (p : Fin n → K) (u : K) : Fin n × ℕ :=
  arithmeticGeneratedMinimumScan l (countedPlannerFirstPrefix l) p u fallback

lemma countedPlannerFirstChoice_value (l : List (Fin n)) (hl : l.Nodup)
    (hA : l.toFinset.Nonempty) (p : Fin n → ℝ) (u : ℝ) :
    (countedPlannerFirstChoice l (l.toFinset.max' hA) p u).1 = plannerFirstSuccessChoice l.toFinset p hA u := by
  rw [countedPlannerFirstChoice, arithmeticGeneratedMinimumScan_value]
  apply arithmeticMinimumScan_eq_categorical l.toFinset hA l (fun _ => List.mem_toFinset.symm)
    (plannerFirstSuccessWeight l.toFinset p)
  intro i _
  rw [countedPlannerFirstPrefix_value, eval_plannerFirstPrefixExpression l hl p]

lemma countedPlannerFirstChoice_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (fallback : Fin n) (p : Fin n → K) (u : K) :
    (countedPlannerFirstChoice l fallback p u).2 ≤ 100 * (l.length + 1) ^ 3 := by
  have h := arithmeticGeneratedMinimumScan_work l (countedPlannerFirstPrefix l) p u fallback
    (2 + 21 * l.length + 29 * l.length ^ 2) (1 + l.length * (16 + 24 * l.length))
    (fun i _ => countedPlannerFirstPrefix_work l i)
    (fun i _ => by rw [countedPlannerFirstPrefix_value]; exact work_plannerFirstPrefixExpression_le l i)
  dsimp only [countedPlannerFirstChoice]
  nlinarith [Nat.zero_le (l.length ^ 2), Nat.zero_le (l.length ^ 3)]

def plannerUniformWeightExpression (N : ℕ) : ArithmeticExpression (Fin n) :=
  .div (.integer 1) (.integer (N : ℤ))

@[simp] lemma work_plannerUniformWeightExpression (N : ℕ) :
    work (@plannerUniformWeightExpression n N) = 3 := rfl

@[simp] lemma eval_plannerUniformWeightExpression (p : Fin n → ℝ) (N : ℕ) :
    eval p (plannerUniformWeightExpression N) = 1 / (N : ℝ) := by
  simp [plannerUniformWeightExpression, eval]

def countedPlannerUniformPrefix (l : List (Fin n)) (i : Fin n) : ArithmeticExpression (Fin n) × ℕ :=
  let N := countedListLength l
  let pref :=  countedPredicateFilter (fun j => j ≤ i) l
  let q := countedSumExpression pref.1 (fun _ => (plannerUniformWeightExpression N.1, 3))
  (q.1, N.2 + pref.2 + q.2)

lemma countedPlannerUniformPrefix_value (l : List (Fin n)) (i : Fin n) :
    (countedPlannerUniformPrefix l i).1 = sumList (l.filter (fun j => decide (j ≤ i)))
      (fun _ => plannerUniformWeightExpression l.length) := by
  simp only [countedPlannerUniformPrefix, countedSumExpression_value,
    countedPredicateFilter_value, countedListLength_value]

lemma countedPlannerUniformPrefix_generation_work (l : List (Fin n)) (i : Fin n) :
    (countedPlannerUniformPrefix l i).2 ≤ 3 + 10 * l.length := by
  have hF := countedPredicateFilter_work (fun j => j ≤ i) l
  have hQ := countedSumExpression_work (countedPredicateFilter (fun j => j ≤ i) l).1
    (fun _ => (@plannerUniformWeightExpression n (countedListLength l).1, 3)) 3 (fun _ _ => le_rfl)
  have hLen : (countedPredicateFilter (fun j => j ≤ i) l).1.length ≤ l.length := by
    rw [countedPredicateFilter_value]
    exact List.length_filter_le _ _
  dsimp only [countedPlannerUniformPrefix]
  rw [countedListLength_work]
  omega

lemma countedPlannerUniformPrefix_expression_work (l : List (Fin n)) (i : Fin n) :
    work (countedPlannerUniformPrefix l i).1 ≤ 1 + 4 * l.length := by
  rw [countedPlannerUniformPrefix_value]
  have h := work_sumList_le (l.filter (fun j => decide (j ≤ i)))
    (fun _ => @plannerUniformWeightExpression n l.length) 3 (fun _ _ => le_rfl)
  have hLen := List.length_filter_le (fun j => decide (j ≤ i)) l
  omega

lemma eval_countedPlannerUniformPrefix (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (i : Fin n) :
    eval p (countedPlannerUniformPrefix l i).1 =
      categoricalPrefix l.toFinset (fun _ => 1 / (l.toFinset.card : ℝ)) i := by
  have hSet : (l.filter (fun j => decide (j ≤ i))).toFinset = l.toFinset.filter (fun j => j ≤ i) := by
    ext j
    simp
  rw [countedPlannerUniformPrefix_value, eval_sumList]
  simp only [eval_plannerUniformWeightExpression]
  rw [← List.sum_toFinset (fun _ : Fin n => 1 / (l.length : ℝ)) (hl.filter _), hSet]
  rw [List.toFinset_card_of_nodup hl]
  rfl

def countedPlannerUniformIdentity {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (fallback : Fin n) (u : K) : Fin n × ℕ :=
  arithmeticGeneratedMinimumScan l (countedPlannerUniformPrefix l) (fun _ : Fin n => (0 : K)) u fallback

lemma countedPlannerUniformIdentity_value (l : List (Fin n)) (hl : l.Nodup)
    (hD : l.toFinset.Nonempty) (u : ℝ) :
    (countedPlannerUniformIdentity l (l.toFinset.max' hD) u).1 = plannerUniformIdentity l.toFinset hD u := by
  rw [countedPlannerUniformIdentity, arithmeticGeneratedMinimumScan_value]
  apply arithmeticMinimumScan_eq_categorical l.toFinset hD l (fun _ => List.mem_toFinset.symm)
    (fun _ => 1 / (l.toFinset.card : ℝ))
  intro i _
  exact eval_countedPlannerUniformPrefix l hl _ i

lemma countedPlannerUniformIdentity_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (fallback : Fin n) (u : K) :
    (countedPlannerUniformIdentity l fallback u).2 ≤ 30 * (l.length + 1) ^ 2 := by
  have h := arithmeticGeneratedMinimumScan_work l (countedPlannerUniformPrefix l)
    (fun _ : Fin n => (0 : K)) u fallback (3 + 10 * l.length) (1 + 4 * l.length)
    (fun i _ => countedPlannerUniformPrefix_generation_work l i)
    (fun i _ => countedPlannerUniformPrefix_expression_work l i)
  dsimp only [countedPlannerUniformIdentity]
  nlinarith

lemma countedMaximumScan_eq_finsetMax (l : List (Fin n)) (hA : l.toFinset.Nonempty)
    (fallback : Fin n) (hf : fallback ∈ l) :
    (countedMaximumScan fallback l).1 = l.toFinset.max' hA := by
  apply le_antisymm
  · exact countedMaximumScan_le fallback l _
      (Finset.le_max' _ _ (List.mem_toFinset.mpr hf))
      (fun i hi => Finset.le_max' _ _ (List.mem_toFinset.mpr hi))
  · exact le_countedMaximumScan_of_mem fallback l
      (List.mem_toFinset.mp (Finset.max'_mem l.toFinset hA))

end ProphetSecretary.Statistics
