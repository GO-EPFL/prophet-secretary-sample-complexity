import ProphetSecretary.Statistics.PlannerSamplerValueMap
import ProphetSecretary.Statistics.ScalarPlannerWork
import ProphetSecretary.Analysis.MultilevelSeedMap

/-!
# Ordered field interpretation of the counted scalar recursion

The projection preserves the stored probabilities, all comparisons, and
the exact state and value produced by each recursive estimate.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ} {K L : Type*} [Field K] [Field L] [LinearOrder K] [LinearOrder L]

def plannerRowsValueMap (f : K → L) (rows : Vector (List K) n) : Vector (List L) n := rows.map (List.map f)

def scalarPlannerStateValueMap (f : K → L) (x : ScalarPlannerListState n K) : ScalarPlannerListState n L :=
  (x.1,f x.2.1,f x.2.2)

def scalarPlannerFrameValueMap (f : K → L) (x : ScalarPlannerFrame n K) : ScalarPlannerFrame n L :=
  ⟨x.active,f x.time,f x.durationWeight,f x.weight,f x.emptyValue,f x.offset,f x.coefficient⟩

variable (f : K →+* L) (hf : StrictMono f)
include hf

private lemma positive_valueMap (x : K) : 0<f x ↔ 0<x := by rw [← map_zero f,hf.lt_iff_lt]

lemma countedPlannerRowProbability_valueMap (l : List K) :
    (countedPlannerRowProbability (l.map f)).1 = f (countedPlannerRowProbability l).1 := by
  have h : (fun x : L => decide (x≤0)) ∘ f = fun x : K => decide (x≤0) := by
    funext x
    have he : f x≤0 ↔ x≤0 := by rw [← map_zero f,hf.le_iff_le]
    simp only [Function.comp_apply,he]
  simp only [countedPlannerRowProbability,countedRowCDFCounts_value,List.length_map,List.countP_map,h,
    map_div₀,map_sub,map_natCast]

omit f hf in
private lemma valueMapVectorGet_ofFn {α : Type*} (g : Fin n → α) (i : Fin n) :
    (Vector.ofFn g).get i = g i := Vector.getElem_ofFn i.isLt

lemma plannerProbabilityRead_valueMap (rows : Vector (List K) n) (i : Fin n) :
    plannerProbabilityRead (countedPlannerProbabilities (plannerRowsValueMap f rows)).1 i =
      f (plannerProbabilityRead (countedPlannerProbabilities rows).1 i) := by
  have h : (plannerRowsValueMap f rows).get i = (rows.get i).map f := by simp [plannerRowsValueMap,Vector.get]
  simp only [plannerProbabilityRead,countedPlannerProbabilities,valueMapVectorGet_ofFn,h,
    countedPlannerRowProbability_valueMap f hf]

lemma countedPlannerActive_valueMap (p : Fin n → K) (l : List (Fin n)) :
    countedPlannerActive (fun i => f (p i)) l = countedPlannerActive p l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [countedPlannerActive,positive_valueMap f hf,ih]

omit hf [LinearOrder K] [LinearOrder L] in
lemma countedPlannerWeight_valueMap (p : Fin n → K) (l : List (Fin n)) :
    (countedPlannerWeight (fun i => f (p i)) l).1 = f (countedPlannerWeight p l).1 := by
  induction l with
  | nil => simp [countedPlannerWeight]
  | cons i l ih => simp [countedPlannerWeight,ih,map_ofNat]

private lemma countedExcessTotals_valueMap (l : List K) (a : K) :
    (countedPlannerExcessTotals (f a) (l.map f)).1 =
      (f (countedPlannerExcessTotals a l).1.1,f (countedPlannerExcessTotals a l).1.2) := by
  induction l with
  | nil => simp [countedPlannerExcessTotals]
  | cons x l ih =>
    by_cases h : 0<x <;> simp [countedPlannerExcessTotals,ih,positive_valueMap f hf,h,hf.monotone.map_max]

lemma countedPlannerExcess_valueMap (l : List K) (a : K) :
    (countedPlannerExcess (l.map f) (f a)).1 = f (countedPlannerExcess l a).1 := by
  simp only [countedPlannerExcess,countedExcessTotals_valueMap f hf,map_div₀]

lemma countedScalarPlannerFrame_valueMap (p : Fin n → K) (x : ScalarPlannerListState n K) :
    (countedScalarPlannerFrame (fun i => f (p i)) (scalarPlannerStateValueMap f x)).1 =
      scalarPlannerFrameValueMap f (countedScalarPlannerFrame p x).1 := by
  simp [countedScalarPlannerFrame,scalarPlannerStateValueMap,scalarPlannerFrameValueMap,
    countedPlannerActive_valueMap f hf,countedPlannerWeight_valueMap f,hf.monotone.map_max,hf.monotone.map_min,map_ofNat]

lemma countedScalarPlannerChild_valueMap (x : ScalarPlannerFrame n K) (o : PlannerListOutput n K) :
    (countedScalarPlannerChild (scalarPlannerFrameValueMap f x) (plannerListOutputMap f o)).1 =
      scalarPlannerStateValueMap f (countedScalarPlannerChild x o).1 := by
  simp [countedScalarPlannerChild,scalarPlannerFrameValueMap,plannerListOutputMap,
    scalarPlannerStateValueMap,hf.monotone.map_max,hf.monotone.map_min]

lemma countedScalarPlannerPayoff_valueMap (rows : Vector (List K) n) (p : Fin n → K)
    (o : PlannerListOutput n K) (a : K) :
    (countedScalarPlannerPayoff (plannerRowsValueMap f rows) (fun i => f (p i)) (plannerListOutputMap f o) (f a)).1 =
      f (countedScalarPlannerPayoff rows p o a).1 := by
  rcases o with ⟨o,s,l⟩
  cases o with
  | none => simp [countedScalarPlannerPayoff,plannerListOutputMap]
  | some i =>
    have h : (plannerRowsValueMap f rows).get i = (rows.get i).map f := by simp [plannerRowsValueMap,Vector.get]
    simp only [countedScalarPlannerPayoff,plannerListOutputMap,countedPlannerActive_valueMap f hf,
      countedPlannerWeight_valueMap f,h,map_div₀]
    rw [← map_mul,countedPlannerExcess_valueMap f hf]

lemma countedScalarPlannerSample_valueMap (p : Fin n → K) (x : ScalarPlannerFrame n K)
    (s : PlannerFieldSeed n K) :
    (countedScalarPlannerSample (fun i => f (p i)) (scalarPlannerFrameValueMap f x) (plannerMapSeed f s)).1 =
      plannerListOutputMap f (countedScalarPlannerSample p x s).1 := by
  simp only [countedScalarPlannerSample,scalarPlannerFrameValueMap,countedPlannerUniformSampler_valueMap f hf]

theorem multilevelEstimate_valueMap
    {State State' Seed Seed' Out Out' : Type*}
    (D : MultilevelRecursion State Seed Out K) (E : MultilevelRecursion State' Seed' Out' L)
    (view : State → State') (seed : Seed → Seed')
    (hFlag : ∀ x, D.isEmpty x = E.isEmpty (view x))
    (hEmpty : ∀ x, f (D.emptyValue x) = E.emptyValue (view x))
    (hOffset : ∀ x, f (D.offset x) = E.offset (view x))
    (hCoefficient : ∀ x, f (D.coefficient x) = E.coefficient (view x))
    (hChild : ∀ x s, view (D.child x (D.sample x s)) = E.child (view x) (E.sample (view x) (seed s)))
    (hPayoff : ∀ x s a, f (D.payoff x (D.sample x s) a) =
      E.payoff (view x) (E.sample (view x) (seed s)) (f a))
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) :
    f (multilevelEstimate D r x t) = multilevelEstimate E r (view x) (multilevelTreeMap seed r t) := by
  have hClip (a : K) : f (clipFive a) = clipFive (f a) := by
    simp [clipFive,hf.monotone.map_max,hf.monotone.map_min,map_ofNat]
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [multilevelEstimate,multilevelTreeMap]
    | @node d base tr up lo =>
      have hu (l : Fin d) (x' : State) (t' : MultilevelTree Seed (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) x' t'
      have hl (l : Fin d) (x' : State) (t' : MultilevelTree Seed l.val) :=
        ih l.val (by have := l.isLt; omega) x' t'
      by_cases he : D.isEmpty x = true
      · have he' : E.isEmpty (view x) = true := (hFlag x).symm.trans he
        simp only [multilevelTreeMap,multilevelEstimate,he,he',if_true,hEmpty]
      · have he' : ¬E.isEmpty (view x) = true := fun h => he ((hFlag x).trans h)
        simp only [multilevelTreeMap,multilevelEstimate,if_neg he,if_neg he',hClip,
          map_add,map_mul,map_div₀,map_one,map_pow,map_ofNat,map_sum,map_sub,map_zero,
          hOffset,hCoefficient,hPayoff,hu,hl,hChild]

theorem countedScalarPlannerEstimate_valueMap (rows : Vector (List K) n) (p : Fin n → K)
    (r : ℕ) (x : ScalarPlannerListState n K) (t : MultilevelTree (PlannerFieldSeed n K) r) :
    f ((countedScalarPlannerRecursion rows p).estimate r x t).1 =
      ((countedScalarPlannerRecursion (plannerRowsValueMap f rows) (fun i => f (p i))).estimate
        r (scalarPlannerStateValueMap f x) (multilevelTreeMap (plannerMapSeed f) r t)).1 := by
  rw [CountedPlannerRecursion.estimate_value,CountedPlannerRecursion.estimate_value]
  apply multilevelEstimate_valueMap f hf _ _ (scalarPlannerStateValueMap f) (plannerMapSeed f)
  all_goals
    intros
    simp only [countedScalarPlannerRecursion,CountedPlannerRecursion.toRecursion,
      countedScalarPlannerFrame_valueMap f hf]
    try rfl
  · rw [countedScalarPlannerSample_valueMap f hf,countedScalarPlannerChild_valueMap f hf]
  · rw [countedScalarPlannerSample_valueMap f hf,countedScalarPlannerPayoff_valueMap f hf]

end ProphetSecretary.Statistics
