import ProphetSecretary.Statistics.PlannerChoiceWork

/-!
# Counted coin and maximum phases of the planner sampler

The first-success coins skip identities preceding the chosen first success.
The tail coins skip identities already selected. Both list filters and the
masked maximum count their actual branches on every raw seed.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability
open ArithmeticExpression

variable {n : ℕ}

def countedPlannerFirstCoins {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (k : Fin n) (u : Fin n → K) : List (Fin n) × ℕ :=
  match l with
  | [] => ([], 1)
  | j :: l =>
      let tail := countedPlannerFirstCoins l p k u
      if k < j then
        let e := plannerProbabilityExpression j
        if u j ≤ eval p e then (j :: tail.1, tail.2 + 2 * work e + 5)
        else (tail.1, tail.2 + 2 * work e + 4)
      else (tail.1, tail.2 + 2)

lemma countedPlannerFirstCoins_value {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (k : Fin n) (u : Fin n → K) :
    (countedPlannerFirstCoins l p k u).1 =
      l.filter (fun j => decide (k < j ∧ u j ≤ eval p (plannerProbabilityExpression j))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    by_cases hj : k < j
    · by_cases hu : u j ≤ eval p (plannerProbabilityExpression j) <;>
        simp [countedPlannerFirstCoins, hj, hu, ih]
    · simp [countedPlannerFirstCoins, hj, ih]

lemma countedPlannerFirstCoins_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (k : Fin n) (u : Fin n → K) :
    (countedPlannerFirstCoins l p k u).2 ≤ 1 + 23 * l.length := by
  induction l with
  | nil => simp [countedPlannerFirstCoins]
  | cons j l ih =>
    dsimp only [countedPlannerFirstCoins]
    split_ifs <;> dsimp only <;>
      simp only [work_plannerProbabilityExpression, List.length_cons] <;> omega

lemma countedPlannerFirstCoins_value_real (l : List (Fin n)) (p : Fin n → ℝ)
    (k : Fin n) (u : Fin n → ℝ) :
    (countedPlannerFirstCoins l p k u).1 =
      l.filter (fun j => decide (k < j ∧ u j ≤ plannerBernoulliProbability (p j))) := by
  rw [countedPlannerFirstCoins_value]
  simp only [eval_plannerProbabilityExpression]

lemma countedPlannerFirstCoins_toFinset (l : List (Fin n)) (p : Fin n → ℝ)
    (k : Fin n) (u : Fin n → ℝ) :
    (countedPlannerFirstCoins l p k u).1.toFinset =
      bernoulliSubset (l.toFinset.filter (fun j => k < j))
        (fun j => plannerBernoulliProbability (p j)) u := by
  ext j
  simp [countedPlannerFirstCoins_value_real, bernoulliSubset, and_assoc]

lemma countedPlannerFirstCoins_firstSuccess (l : List (Fin n)) (p : Fin n → ℝ)
    (k : Fin n) (u : Fin n → ℝ) :
    (k :: (countedPlannerFirstCoins l p k u).1).toFinset = plannerFirstSuccessSet l.toFinset p k u := by
  rw [List.toFinset_cons, countedPlannerFirstCoins_toFinset]
  rfl

def countedPlannerFraction {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (u : Fin n → K) : K × ℕ :=
  let q := countedMaximumExpression l (fun j => (.input j, 1))
  let e := ArithmeticExpression.minimum q.1 (.integer 1)
  (eval u e, q.2 + 2 + work e)

lemma eval_plannerMaximumList {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (u : Fin n → K) :
    eval u (maximumList l (fun j => .input j)) = (countedMaximumScan (0 : K) (l.map u)).1 := by
  induction l with
  | nil => simp [maximumList, eval, countedMaximumScan]
  | cons j l ih =>
    change max (u j) (eval u (maximumList l (fun j => .input j))) =
      max (u j) (countedMaximumScan (0 : K) (l.map u)).1
    rw [ih]

lemma countedPlannerFraction_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (u : Fin n → K) : (countedPlannerFraction l u).2 ≤ 6 + 5 * l.length := by
  have hg := countedMaximumExpression_work l (fun j : Fin n => (.input j, 1)) 1 (fun _ _ => le_rfl)
  have he : work (countedMaximumExpression l (fun j : Fin n => (.input j, 1))).1 ≤
      1 + l.length * (1 + 1) := by
    rw [countedMaximumExpression_value]
    exact work_maximumList_le l (fun j : Fin n => ArithmeticExpression.input j) 1 (fun _ _ => le_rfl)
  dsimp only [countedPlannerFraction]
  change (countedMaximumExpression l (fun j : Fin n => (.input j, 1))).2 + 2 +
    (work (countedMaximumExpression l (fun j : Fin n => (.input j, 1))).1 + 1 + 1) ≤ _
  omega

lemma plannerMaximumList_eq_max_zero (l : List (Fin n)) (hD : l.toFinset.Nonempty)
    (u : Fin n → ℝ) : eval u (maximumList l (fun j => .input j)) =
      max 0 (uniformSubsetMaximum l.toFinset hD u) := by
  rw [eval_plannerMaximumList]
  apply le_antisymm
  · apply countedMaximumScan_le 0 (l.map u) _ (le_max_left _ _)
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact (Finset.le_sup' u (List.mem_toFinset.mpr hj)).trans (le_max_right _ _)
  · apply max_le (le_countedMaximumScan_fallback 0 (l.map u))
    change l.toFinset.sup' hD u ≤ _
    apply Finset.sup'_le
    intro j hj
    exact le_countedMaximumScan_of_mem 0 (l.map u) (List.mem_map.mpr ⟨j, List.mem_toFinset.mp hj, rfl⟩)

lemma countedPlannerFraction_value (l : List (Fin n)) (hD : l.toFinset.Nonempty)
    (u : Fin n → ℝ) : (countedPlannerFraction l u).1 = plannerUnitFraction l.toFinset hD u := by
  simp only [countedPlannerFraction, countedMaximumExpression_value, eval]
  rw [plannerMaximumList_eq_max_zero l hD u]
  unfold plannerUnitFraction
  rw [min_max_distrib_right]
  norm_num

def countedPlannerTailCoins {K : Type*} [LinearOrder K]
    (l D : List (Fin n)) (s : K) (u : Fin n → K) : List (Fin n) × ℕ :=
  match l with
  | [] => ([], 1)
  | j :: l =>
      let tail := countedPlannerTailCoins l D s u
      let membership := countedListContains j D
      if membership.1 then (tail.1, tail.2 + membership.2 + 1)
      else if u j ≤ s then (j :: tail.1, tail.2 + membership.2 + 4)
      else (tail.1, tail.2 + membership.2 + 3)

lemma countedPlannerTailCoins_value {K : Type*} [LinearOrder K]
    (l D : List (Fin n)) (s : K) (u : Fin n → K) :
    (countedPlannerTailCoins l D s u).1 = l.filter (fun j => decide (j ∉ D ∧ u j ≤ s)) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    by_cases hj : j ∈ D
    · simp [countedPlannerTailCoins, countedListContains_value, hj, ih]
    · by_cases hu : u j ≤ s <;> simp [countedPlannerTailCoins, countedListContains_value, hj, hu, ih]

lemma countedPlannerTailCoins_work {K : Type*} [LinearOrder K]
    (l D : List (Fin n)) (s : K) (u : Fin n → K) :
    (countedPlannerTailCoins l D s u).2 ≤ 1 + l.length * (2 * D.length + 5) := by
  induction l with
  | nil => simp [countedPlannerTailCoins]
  | cons j l ih =>
    have hm := countedListContains_work j D
    dsimp only [countedPlannerTailCoins]
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> nlinarith

lemma countedPlannerTailCoins_toFinset (l D : List (Fin n)) (s : ℝ) (u : Fin n → ℝ) :
    (countedPlannerTailCoins l D s u).1.toFinset =
      bernoulliSubset (l.toFinset \ D.toFinset) (fun _ => s) u := by
  ext j
  simp [countedPlannerTailCoins_value, bernoulliSubset, and_assoc]

def countedAppend {α : Type*} : List α → List α → List α × ℕ
  | [], b => (b, 1)
  | a :: l, b => let q := countedAppend l b; (a :: q.1, q.2 + 2)

lemma countedAppend_value {α : Type*} (a b : List α) : (countedAppend a b).1 = a ++ b := by
  induction a with
  | nil => rfl
  | cons i l ih => simp [countedAppend, ih]

lemma countedAppend_work {α : Type*} (a b : List α) : (countedAppend a b).2 = 1 + 2 * a.length := by
  induction a with
  | nil => rfl
  | cons i l ih => simp only [countedAppend, ih, List.length_cons]; omega

end ProphetSecretary.Statistics
