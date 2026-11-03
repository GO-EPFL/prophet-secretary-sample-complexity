import ProphetSecretary.Statistics.PlannerSamplerRatCast
import ProphetSecretary.Statistics.ScalarPlannerWork
import ProphetSecretary.Analysis.MultilevelSeedMap

/-!
# Exact rational evaluation of the scalar planner

On rational inputs, every primitive computation agrees with its real
interpretation. In particular, this transport introduces no additional
approximation of the value or of the comparisons in the sampler.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ} {k : Fin n → ℕ}

def plannerRowsRatCast (rows : Vector (List ℚ) n) : Vector (List ℝ) n :=
  rows.map (List.map fun x : ℚ => (x : ℝ))

def scalarPlannerStateRatCast (x : ScalarPlannerListState n ℚ) : ScalarPlannerListState n ℝ :=
  (x.1, (x.2.1, x.2.2))

def scalarPlannerFrameRatCast (q : ScalarPlannerFrame n ℚ) : ScalarPlannerFrame n ℝ :=
  ⟨q.active, q.time, q.durationWeight, q.weight, q.emptyValue, q.offset, q.coefficient⟩

@[simp] lemma plannerRowsRatCast_get (rows : Vector (List ℚ) n) (i : Fin n) :
    (plannerRowsRatCast rows).get i = (rows.get i).map fun x : ℚ => (x : ℝ) := by
  simp [plannerRowsRatCast, Vector.get]

lemma plannerRowsRatCast_ofFn (y : (i : Fin n) → Fin (k i) → ℚ) :
    plannerRowsRatCast (plannerStoredRows y) = plannerStoredRows (fun i j => (y i j : ℝ)) := by
  apply Vector.ext
  intro i hi
  change (plannerRowsRatCast (plannerStoredRows y)).get ⟨i, hi⟩ =
    (plannerStoredRows (fun i j => (y i j : ℝ))).get ⟨i, hi⟩
  simp [List.map_ofFn, Function.comp_def]

lemma countedPlannerRowProbability_ratCast (row : List ℚ) :
    (countedPlannerRowProbability (row.map fun x : ℚ => (x : ℝ))).1 =
      ((countedPlannerRowProbability row).1 : ℝ) := by
  have he : (fun x : ℝ => decide (x ≤ 0)) ∘ (fun x : ℚ => (x : ℝ)) = fun x : ℚ => decide (x ≤ 0) := by
    funext x
    simp
  simp only [countedPlannerRowProbability, countedRowCDFCounts_value, List.length_map,
    List.countP_map, he, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast]

private lemma vectorGet_ofFn {α : Type*} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

lemma plannerProbabilityRead_ratCast (rows : Vector (List ℚ) n) (i : Fin n) :
    plannerProbabilityRead (countedPlannerProbabilities (plannerRowsRatCast rows)).1 i =
      ((plannerProbabilityRead (countedPlannerProbabilities rows).1 i : ℚ) : ℝ) := by
  simp only [plannerProbabilityRead, countedPlannerProbabilities, vectorGet_ofFn, plannerRowsRatCast_get,
    countedPlannerRowProbability_ratCast]

lemma countedPlannerActive_ratCast (p : Fin n → ℚ) (l : List (Fin n)) :
    countedPlannerActive (fun i => (p i : ℝ)) l = countedPlannerActive p l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [countedPlannerActive, Rat.cast_pos, ih]

lemma countedPlannerWeight_ratCast (p : Fin n → ℚ) (l : List (Fin n)) :
    (countedPlannerWeight (fun i => (p i : ℝ)) l).1 = ((countedPlannerWeight p l).1 : ℝ) := by
  induction l with
  | nil => simp [countedPlannerWeight]
  | cons i l ih => simp [countedPlannerWeight, ih]

private lemma excessTotals_ratCast (row : List ℚ) (v : ℚ) :
    (countedPlannerExcessTotals (v : ℝ) (row.map fun x : ℚ => (x : ℝ))).1 =
      (((countedPlannerExcessTotals v row).1.1 : ℝ), ((countedPlannerExcessTotals v row).1.2 : ℝ)) := by
  induction row with
  | nil => simp [countedPlannerExcessTotals]
  | cons x row ih =>
    by_cases hx : 0 < x <;>
      simp [countedPlannerExcessTotals, ih, hx, Rat.cast_max]

lemma countedPlannerExcess_ratCast (row : List ℚ) (v : ℚ) :
    (countedPlannerExcess (row.map fun x : ℚ => (x : ℝ)) (v : ℝ)).1 =
      ((countedPlannerExcess row v).1 : ℝ) := by
  simp only [countedPlannerExcess, excessTotals_ratCast, Rat.cast_div]

lemma countedScalarPlannerFrame_ratCast (p : Fin n → ℚ) (x : ScalarPlannerListState n ℚ) :
    (countedScalarPlannerFrame (fun i => (p i : ℝ)) (scalarPlannerStateRatCast x)).1 =
      scalarPlannerFrameRatCast (countedScalarPlannerFrame p x).1 := by
  simp [countedScalarPlannerFrame, scalarPlannerStateRatCast, scalarPlannerFrameRatCast,
    countedPlannerActive_ratCast, countedPlannerWeight_ratCast, Rat.cast_max, Rat.cast_min]

lemma countedScalarPlannerChild_ratCast (q : ScalarPlannerFrame n ℚ) (o : PlannerListOutput n ℚ) :
    (countedScalarPlannerChild (scalarPlannerFrameRatCast q) (plannerListOutputRatCast o)).1 =
      scalarPlannerStateRatCast (countedScalarPlannerChild q o).1 := by
  simp [countedScalarPlannerChild, scalarPlannerFrameRatCast, plannerListOutputRatCast,
    scalarPlannerStateRatCast, Rat.cast_max, Rat.cast_min]

lemma countedScalarPlannerPayoff_ratCast (rows : Vector (List ℚ) n) (p : Fin n → ℚ)
    (o : PlannerListOutput n ℚ) (a : ℚ) :
    (countedScalarPlannerPayoff (plannerRowsRatCast rows) (fun i => (p i : ℝ))
      (plannerListOutputRatCast o) (a : ℝ)).1 =
        ((countedScalarPlannerPayoff rows p o a).1 : ℝ) := by
  rcases o with ⟨o, s, l⟩
  cases o <;>
    simp [countedScalarPlannerPayoff, plannerListOutputRatCast, countedPlannerActive_ratCast,
      countedPlannerWeight_ratCast, ← Rat.cast_mul, countedPlannerExcess_ratCast]

lemma countedScalarPlannerSample_ratCast (p : Fin n → ℚ) (q : ScalarPlannerFrame n ℚ)
    (s : PlannerFieldSeed n ℚ) :
    (countedScalarPlannerSample (fun i => (p i : ℝ)) (scalarPlannerFrameRatCast q)
      (plannerFieldSeedRatCast s)).1 =
        plannerListOutputRatCast (countedScalarPlannerSample p q s).1 := by
  simp only [countedScalarPlannerSample, scalarPlannerFrameRatCast, countedPlannerUniformSampler_ratCast]

private lemma ratCast_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ((∑ i ∈ s, f i : ℚ) : ℝ) = ∑ i ∈ s, (f i : ℝ) :=
  map_sum (Rat.castHom ℝ) f s

private lemma ratCast_clipFive (a : ℚ) : ((clipFive a : ℚ) : ℝ) = clipFive (a : ℝ) := by
  simp [clipFive, Rat.cast_max, Rat.cast_min]

/-- Transport an estimator across the inclusion of rational values into
reals and a corresponding change of state and seed representations. -/
theorem multilevelEstimate_ratCast_transport
    {State State' Seed Seed' Out Out' : Type*}
    (D : MultilevelRecursion State Seed Out ℚ) (E : MultilevelRecursion State' Seed' Out' ℝ)
    (view : State → State') (f : Seed → Seed')
    (hFlag : ∀ x, D.isEmpty x = E.isEmpty (view x))
    (hEmpty : ∀ x, (D.emptyValue x : ℝ) = E.emptyValue (view x))
    (hOffset : ∀ x, (D.offset x : ℝ) = E.offset (view x))
    (hCoefficient : ∀ x, (D.coefficient x : ℝ) = E.coefficient (view x))
    (hChild : ∀ x s, view (D.child x (D.sample x s)) = E.child (view x) (E.sample (view x) (f s)))
    (hPayoff : ∀ x s a, (D.payoff x (D.sample x s) a : ℝ) =
      E.payoff (view x) (E.sample (view x) (f s)) (a : ℝ))
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) :
    ((multilevelEstimate D r x t : ℚ) : ℝ) = multilevelEstimate E r (view x) (multilevelTreeMap f r t) := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [multilevelEstimate, multilevelTreeMap]
    | @node d base tr up lo =>
      have hu (l : Fin d) (x' : State) (t' : MultilevelTree Seed (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) x' t'
      have hl (l : Fin d) (x' : State) (t' : MultilevelTree Seed l.val) :=
        ih l.val (by have := l.isLt; omega) x' t'
      by_cases he : D.isEmpty x = true
      · have he' : E.isEmpty (view x) = true := (hFlag x).symm.trans he
        simp only [multilevelTreeMap, multilevelEstimate, he, he', if_true, hEmpty]
      · have he' : ¬ E.isEmpty (view x) = true := fun h => he ((hFlag x).trans h)
        simp only [multilevelTreeMap, multilevelEstimate, if_neg he, if_neg he', ratCast_clipFive,
          Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
          ratCast_finset_sum, Rat.cast_sub, Rat.cast_zero, hOffset, hCoefficient,
          hPayoff, hu, hl, hChild]

/-- The counted rational estimator has exactly the value of the counted
real estimator after embedding the rows, state, and transition seeds. -/
theorem countedScalarPlannerEstimate_ratCast (rows : Vector (List ℚ) n) (p : Fin n → ℚ)
    (r : ℕ) (x : ScalarPlannerListState n ℚ) (t : MultilevelTree (PlannerFieldSeed n ℚ) r) :
    (((countedScalarPlannerRecursion rows p).estimate r x t).1 : ℝ) =
      ((countedScalarPlannerRecursion (plannerRowsRatCast rows) (fun i => (p i : ℝ))).estimate
        r (scalarPlannerStateRatCast x) (multilevelTreeMap plannerFieldSeedRatCast r t)).1 := by
  rw [CountedPlannerRecursion.estimate_value, CountedPlannerRecursion.estimate_value]
  apply multilevelEstimate_ratCast_transport _ _ scalarPlannerStateRatCast plannerFieldSeedRatCast
  all_goals
    intros
    simp only [countedScalarPlannerRecursion, CountedPlannerRecursion.toRecursion,
      countedScalarPlannerFrame_ratCast]
    try rfl
  · rw [countedScalarPlannerSample_ratCast, countedScalarPlannerChild_ratCast]
  · rw [countedScalarPlannerSample_ratCast, countedScalarPlannerPayoff_ratCast]

/-- The rational program evaluates the paper's empirical multilevel
estimator at the embedded seed. -/
theorem countedScalarPlannerEstimate_ratCast_value (y : (i : Fin n) → Fin (k i) → ℚ)
    (r : ℕ) (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (t : MultilevelTree (PlannerFieldSeed n ℚ) r) :
    (((countedScalarPlannerRecursion (plannerStoredRows y)
      (plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows y)).1)).estimate r x t).1 : ℝ) =
      multilevelEstimate (scalarPlannerRecursion (fun i j => (y i j : ℝ))) r
        (scalarPlannerListInterpret (scalarPlannerStateRatCast x)) (multilevelTreeMap plannerFieldSeedRatCast r t) := by
  rw [countedScalarPlannerEstimate_ratCast, plannerRowsRatCast_ofFn]
  apply countedScalarPlannerEstimate_value _ _ _ _ _ hx
  funext i
  rw [← plannerProbabilityRead_ratCast, plannerRowsRatCast_ofFn, countedPlannerProbabilities_ofFn]
  rfl

end ProphetSecretary.Statistics
