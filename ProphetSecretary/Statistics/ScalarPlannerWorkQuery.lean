import ProphetSecretary.Statistics.ScalarPlannerWork
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Arithmetic work of the scalar planner query

The query computes its root weight from stored rows, chooses the accuracy
level by arithmetic search, and then runs the counted confidence query.
The tree factor and confidence count are bounded separately.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability ProphetSecretary.Model

variable {n : ℕ} {k : Fin n → ℕ} {Value : Type*}

def storedScalarPlannerWeight [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (x : ScalarPlannerListState n Value) : Value :=
  let q := countedPlannerProbabilities rows
  (countedScalarPlannerFrame (plannerProbabilityRead q.1) x).1.weight

lemma storedScalarPlannerWeight_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) :
    storedScalarPlannerWeight (plannerStoredRows y) x = scalarPlannerWeight y (scalarPlannerListInterpret x).1 := by
  have hp : plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows y)).1 =
      plannerPositiveProbability y := by
    funext i
    exact countedPlannerProbabilities_ofFn y i
  exact countedScalarPlannerFrame_weight y _ hp x hx

/-- Actual query with arithmetic level selection. The supplied seed arrays
have the selected finite shape. The empty-state branch reads none of them. -/
def countedScalarPlannerQuery [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]
    (rows : Vector (List Value) n) (x : ScalarPlannerListState n Value) (h pFail : Value)
    (Hlevel : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ scalarPlannerPrecisionRatio (storedScalarPlannerWeight rows x) h)
    (Hconf : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ pFail)
    (seed : Fin (confidenceCopyCount pFail Hconf) → MultilevelTree (PlannerFieldSeed n Value)
      (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1) : MedianCopiesResult Value :=
  let prepared := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prepared.1) x
  if frame.1.active.isEmpty then
    { value := frame.1.emptyValue, work := prepared.2 + frame.2 + 2, copies := 0 }
  else
    let level := countedScalarPlannerLevel frame.1.weight h Hlevel
    let q := countedScalarPlannerQueryAtLevel rows x level.1 pFail Hconf seed
    { q with work := prepared.2 + frame.2 + level.2 + q.work + 2 }

lemma countedScalarPlannerQuery_value [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]
    (rows : Vector (List Value) n) (x : ScalarPlannerListState n Value) (h pFail : Value)
    (Hlevel : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ scalarPlannerPrecisionRatio (storedScalarPlannerWeight rows x) h)
    (Hconf : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ pFail)
    (seed : Fin (confidenceCopyCount pFail Hconf) → MultilevelTree (PlannerFieldSeed n Value)
      (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1) :
    (countedScalarPlannerQuery rows x h pFail Hlevel Hconf seed).value =
      (countedScalarPlannerQueryAtLevel rows x
        (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1 pFail Hconf seed).value := by
  unfold countedScalarPlannerQuery countedScalarPlannerQueryAtLevel
  dsimp only
  split_ifs <;> rfl

/-- A bound expressed using the selected level and copy count. It includes
both the root preparation and the subsequent confidence-query work. -/
theorem countedScalarPlannerQuery_work [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]
    (rows : Vector (List Value) n) (m : ℕ) (hRows : ∀ i, (rows.get i).length ≤ m)
    (x : ScalarPlannerListState n Value) (hx : x.1.Nodup) (h pFail : Value)
    (Hlevel : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ scalarPlannerPrecisionRatio (storedScalarPlannerWeight rows x) h)
    (Hconf : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ pFail)
    (seed : Fin (confidenceCopyCount pFail Hconf) → MultilevelTree (PlannerFieldSeed n Value)
      (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1) :
    let r := (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1
    let C := confidenceCopyCount pFail Hconf
    (countedScalarPlannerQuery rows x h pFail Hlevel Hconf seed).work ≤
      40 * (n + 1) * (m + 1) + 80 * (n + 1) +
        C * (400 * scalarPlannerPrimitiveBound n m * 16 ^ r + 3) + 10 * (C + 1) ^ 2 + (3 * r + 28) := by
  dsimp only
  let prepared := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prepared.1) x
  let level := countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel
  have hPrep : prepared.2 ≤ 20 * (n + 1) * (m + 1) := countedPlannerProbabilities_work rows m hRows
  have hFrame : frame.2 ≤ 40 * (n + 1) :=
    countedScalarPlannerFrame_work (plannerProbabilityRead prepared.1) x hx
  have hLevel : level.2 ≤ 3 * level.1 + 21 := countedScalarPlannerLevel_work _ h Hlevel
  have hQuery := countedScalarPlannerQueryAtLevel_work rows m hRows x hx level.1 pFail Hconf seed
  change _ ≤
    40 * (n + 1) * (m + 1) + 80 * (n + 1) +
      confidenceCopyCount pFail Hconf * (400 * scalarPlannerPrimitiveBound n m * 16 ^ level.1 + 3) +
      10 * (confidenceCopyCount pFail Hconf + 1) ^ 2 + (3 * level.1 + 28)
  have hPrep2 : 40 * (n+1) * (m+1) = 2 * (20 * (n+1) * (m+1)) := by ring
  rw [hPrep2]
  unfold countedScalarPlannerQuery
  dsimp only
  by_cases he : frame.1.active.isEmpty = true
  · change (if frame.1.active.isEmpty then _ else _ : MedianCopiesResult Value).work ≤ _
    rw [if_pos he]
    change prepared.2 + frame.2 + 2 ≤ _
    omega
  · change (if frame.1.active.isEmpty then _ else _ : MedianCopiesResult Value).work ≤ _
    rw [if_neg he]
    change prepared.2 + frame.2 + level.2 +
      (countedScalarPlannerQueryAtLevel rows x level.1 pFail Hconf seed).work + 2 ≤ _
    omega

/-- Error and actual arithmetic work of the query on empirical input. The
work factor is explicit before expressing its asymptotic dependence. -/
theorem countedScalarPlannerQuery_correct [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1)
    (m : ℕ) (hk : ∀ i, k i ≤ m) (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup)
    (h pFail : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1) (hp : pFail ∈ Ioo (0 : ℝ) (1/2))
    (Hlevel : ∃ j : ℕ, (1 / 4 : ℝ) ^ j ≤ scalarPlannerPrecisionRatio
      (storedScalarPlannerWeight (plannerStoredRows y) x) h)
    (Hconf : ∃ j : ℕ, (1 / 4 : ℝ) ^ j ≤ pFail) :
    let β := storedScalarPlannerWeight (plannerStoredRows y) x
    let r := (countedScalarPlannerLevel β h Hlevel).1
    let C := confidenceCopyCount pFail Hconf
    let call := countedScalarPlannerQuery (plannerStoredRows y) x h pFail Hlevel Hconf
    Measurable (fun seed => (call seed).value) ∧
      (Measure.pi (fun _ : Fin C => multilevelTreeLaw (plannerUniformSeedLaw n) r)).real
        {seed | h < |(call seed).value - scalarPlannerValue y hy (scalarPlannerListInterpret x)|} ≤ pFail ∧
      (16 : ℝ) ^ r ≤ (6400 : ℝ) ^ 4 * (β/h)^8 ∧
      (C : ℝ) < 2 * (Real.log (1/pFail) / Real.log 4) + 3 ∧
      ∀ seed, (call seed).work ≤
        40 * (n + 1) * (m + 1) + 80 * (n + 1) +
          C * (400 * scalarPlannerPrimitiveBound n m * 16 ^ r + 3) + 10 * (C + 1) ^ 2 + (3 * r + 28) := by
  dsimp only
  let β := storedScalarPlannerWeight (plannerStoredRows y) x
  let r := (countedScalarPlannerLevel β h Hlevel).1
  have hβ : β = scalarPlannerWeight y (scalarPlannerListInterpret x).1 := storedScalarPlannerWeight_value y x hx
  have hb : 1 ≤ β := by rw [hβ]; exact scalarPlannerWeight_ge_one _ _
  have hp1 : pFail < 1 := hp.2.trans (by norm_num)
  have hPrec := countedScalarPlannerLevel_error hb hh Hlevel
  have hPrec' : 25 * (scalarPlannerWeight y (scalarPlannerListInterpret x).1)^2 * (1/2 : ℝ)^r ≤ h^2/64 := by
    rw [← hβ]
    exact hPrec
  have hc := countedScalarPlannerQueryAtLevel_correct y hy hcap m hk x hx r h pFail hh.1 hp.1 hp1 Hconf hPrec'
  refine ⟨?_, ?_, countedScalarPlannerLevel_tree_factor hb hh Hlevel,
    confidenceCopyCount_log_bound hp.1 hp1 Hconf, ?_⟩
  · simp_rw [countedScalarPlannerQuery_value]
    exact hc.1
  · simp_rw [countedScalarPlannerQuery_value]
    exact hc.2.1
  · intro seed
    exact countedScalarPlannerQuery_work (plannerStoredRows y) m (fun i => by simpa using hk i)
      x hx h pFail Hlevel Hconf seed

/-- The weight factor is bounded by the total positive probability of the
stored empirical instance. -/
lemma storedScalarPlannerWeight_le_exp (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) :
    storedScalarPlannerWeight (plannerStoredRows y) x ≤ Real.exp (4 * ∑ i, plannerPositiveProbability y i) := by
  rw [storedScalarPlannerWeight_value y x hx]
  unfold scalarPlannerWeight
  refine (plannerWeight_le_exp _ _ (fun i _ => plannerPositiveProbability_nonnegative y i)).trans ?_
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => plannerPositiveProbability_nonnegative y i)

lemma storedScalarPlannerWeight_le_exp_count [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) :
    storedScalarPlannerWeight (plannerStoredRows y) x ≤
      Real.exp (4 * (empiricalPlannerInstance y hy).positiveCount) := by
  change storedScalarPlannerWeight (plannerStoredRows y) x ≤
    Real.exp (4 * ∑ i, (empiricalLaw (y i)).real (Ioi 0))
  simp_rw [empiricalLaw_positiveProbability]
  exact storedScalarPlannerWeight_le_exp y x hx

/-- The explicit tree factor has exponent `32 L(Q)` and degree eight in
inverse accuracy. -/
theorem countedScalarPlannerLevel_tree_factor_exp [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1)
    (Hlevel : ∃ j : ℕ, (1 / 4 : ℝ) ^ j ≤ scalarPlannerPrecisionRatio
      (storedScalarPlannerWeight (plannerStoredRows y) x) h) :
    (16 : ℝ) ^ (countedScalarPlannerLevel (storedScalarPlannerWeight (plannerStoredRows y) x) h Hlevel).1 ≤
      (6400 : ℝ) ^ 4 * Real.exp (32 * (empiricalPlannerInstance y hy).positiveCount) / h ^ 8 := by
  let β := storedScalarPlannerWeight (plannerStoredRows y) x
  let L := (empiricalPlannerInstance y hy).positiveCount
  have hb : 1 ≤ β := by
    dsimp only [β]
    rw [storedScalarPlannerWeight_value y x hx]
    exact scalarPlannerWeight_ge_one _ _
  have hbExp : β ≤ Real.exp (4 * L) := storedScalarPlannerWeight_le_exp_count y hy x hx
  have hPow : β ^ 8 ≤ Real.exp (4 * L) ^ 8 :=
    pow_le_pow_left₀ (zero_le_one.trans hb) hbExp 8
  have hExp : Real.exp (4 * L) ^ 8 = Real.exp (32 * L) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ (6400 : ℝ) ^ 4 * (β / h) ^ 8 := countedScalarPlannerLevel_tree_factor hb hh Hlevel
    _ = (6400 : ℝ) ^ 4 * (β ^ 8 / h ^ 8) := by rw [div_pow]
    _ ≤ (6400 : ℝ) ^ 4 * (Real.exp (4 * L) ^ 8 / h ^ 8) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hPow (by positivity)) (by positivity)
    _ = _ := by rw [hExp, mul_div_assoc]

end ProphetSecretary.Statistics
