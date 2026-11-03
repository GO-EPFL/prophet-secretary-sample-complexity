import ProphetSecretary.Statistics.BinarySamplerScan
import ProphetSecretary.Statistics.PlannerSamplerValueMap
import ProphetSecretary.Statistics.PlannerSamplerRationalHeight

/-!
# The planner transition with counted binary comparisons

The subset and identity scans use the same prefix expressions as the
native sampler. The tail uses its computed fraction, with a separate
comparison for each remaining identity.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

def countedBinaryFilter {α : Type*} (test : α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([],1)
  | a::l =>
    let q := countedBinaryFilter test l
    let c := test a
    (if c.1 then a::q.1 else q.1,q.2+c.2+3)

lemma countedBinaryFilter_value {α : Type*} (test : α → Bool × ℕ) (l : List α) :
    (countedBinaryFilter test l).1=l.filter (fun i => (test i).1) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    cases h : (test i).1 <;> simp [countedBinaryFilter,h,ih]

lemma countedBinaryFilter_work {α : Type*} (test : α → Bool × ℕ) (l : List α) (W : ℕ)
    (h : ∀ i ∈ l, (test i).2≤W) :
    (countedBinaryFilter test l).2≤1+l.length*(W+3) := by
  induction l with
  | nil => simp [countedBinaryFilter]
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have hl := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [countedBinaryFilter,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

variable {n : ℕ}

def binaryFirstCoinTest (p : Fin n → BinaryRational) (k : Fin n) (u : Fin n → BinaryRational)
    (i : Fin n) : Bool × ℕ :=
  if k < i then
    let v := countedBinaryEval (fun j => (p j).storage) (plannerProbabilityExpression i)
    let q := (u i).storage.countedLE v.1
    (q.1,v.2+q.2+3)
  else (false,1)

lemma binaryFirstCoinTest_value (p : Fin n → BinaryRational) (k : Fin n) (u : Fin n → BinaryRational)
    (i : Fin n) : (binaryFirstCoinTest p k u i).1 =
      decide (k < i ∧ (u i).value ≤ eval (fun j => (p j).value) (plannerProbabilityExpression i)) := by
  unfold binaryFirstCoinTest
  split_ifs with h
  · have hv := countedBinaryEval_semantics (fun j => (p j).storage)
      (fun j => BinaryRational.storage_denominator_pos (p j)) (plannerProbabilityExpression i)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,h,true_and]
    have hv' : (countedBinaryEval (fun j => (p j).storage) (plannerProbabilityExpression i)).1.value =
        eval (fun j => (p j).value) (plannerProbabilityExpression i) := hv.1
    exact (BinaryFraction.countedLE_correct _ _ (BinaryRational.storage_denominator_pos (u i)) hv.2).trans
      (by rw [hv']; rfl)
  · simp [h]

def countedBinaryPlannerFraction (l : List (Fin n)) (u : Fin n → BinaryRational) : BinaryRational × ℕ :=
  let q := countedMaximumExpression l (fun j => (.input j,1))
  let v := countedBinaryEval (fun i => (u i).storage) (.minimum q.1 (.integer 1))
  have hv := (countedBinaryEval_semantics (fun i => (u i).storage)
    (fun i => BinaryRational.storage_denominator_pos (u i)) (.minimum q.1 (.integer 1))).2
  let r := BinaryRational.ofFraction v.1 hv
  (r,q.2+v.2+v.1.countedReduce.2+5)

lemma countedBinaryPlannerFraction_value (l : List (Fin n)) (u : Fin n → BinaryRational) :
    (countedBinaryPlannerFraction l u).1.value = (countedPlannerFraction l (fun i => (u i).value)).1 := by
  unfold countedBinaryPlannerFraction countedPlannerFraction
  rw [BinaryRational.ofFraction_value]
  exact (countedBinaryEval_semantics (fun i => (u i).storage)
    (fun i => BinaryRational.storage_denominator_pos (u i)) _).1

def binaryTailCoinTest (D : List (Fin n)) (s : BinaryRational) (u : Fin n → BinaryRational)
    (i : Fin n) : Bool × ℕ :=
  let mem := countedListContains i D
  if mem.1 then (false,mem.2+2) else
    let q := (u i).storage.countedLE s.storage
    (q.1,mem.2+q.2+3)

lemma binaryTailCoinTest_value (D : List (Fin n)) (s : BinaryRational) (u : Fin n → BinaryRational)
    (i : Fin n) : (binaryTailCoinTest D s u i).1 = decide (i∉D ∧ (u i).value≤s.value) := by
  unfold binaryTailCoinTest
  dsimp only
  rw [countedListContains_value]
  by_cases h : i∈D
  · simp [h]
  · simp only [h,decide_false,Bool.false_eq_true,if_false,not_false_eq_true,true_and]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact BinaryFraction.countedLE_correct _ _ (BinaryRational.storage_denominator_pos (u i))
      (BinaryRational.storage_denominator_pos s)

def countedBinarySamplerBody (l : List (Fin n)) (a : Fin n) (p : Fin n → BinaryRational)
    (seed : PlannerFieldSeed n BinaryRational) : PlannerListOutput n BinaryRational × ℕ :=
  let maximum := countedMaximumScan a l
  let first := countedBinaryMinimumScan (countedPlannerFirstPrefix l) p seed.1.1 maximum.1 l
  let coins := countedBinaryFilter (binaryFirstCoinTest p first.1 seed.1.2) l
  let D := first.1::coins.1
  let fallback := countedMaximumScan first.1 D
  let i := countedBinaryMinimumScan (countedPlannerUniformPrefix D) (fun _ => BinaryRational.ofRat 0)
    seed.2.1 fallback.1 D
  let s := countedBinaryPlannerFraction D seed.2.2.1
  let tail := countedBinaryFilter (binaryTailCoinTest D s.1 seed.2.2.2) l
  let companions := countedPredicateFilter (fun j => j≠i.1) D
  let output := countedAppend companions.1 tail.1
  ((some i.1,s.1,output.1),maximum.2+first.2+coins.2+fallback.2+i.2+s.2+tail.2+companions.2+output.2+10)

def countedBinaryUniformSampler (l : List (Fin n)) (p : Fin n → BinaryRational)
    (seed : PlannerFieldSeed n BinaryRational) : PlannerListOutput n BinaryRational × ℕ :=
  match l with
  | [] => ((none,BinaryRational.ofRat 0,[]),1)
  | a::l => countedBinarySamplerBody (a::l) a p seed

theorem countedBinaryUniformSampler_value (l : List (Fin n)) (p : Fin n → BinaryRational)
    (s : PlannerFieldSeed n BinaryRational) :
    plannerListOutputMap BinaryRational.value (countedBinaryUniformSampler l p s).1 =
      (countedPlannerUniformSampler l (fun i => (p i).value) (plannerMapSeed BinaryRational.value s)).1 := by
  cases l with
  | nil => simp [countedBinaryUniformSampler,countedPlannerUniformSampler,plannerListOutputMap]
  | cons a l =>
    simp only [countedBinaryUniformSampler,countedBinarySamplerBody,countedPlannerUniformSampler,
      countedPlannerUniformSamplerBody,countedPlannerFirstStage,plannerMapSeed,plannerListOutputMap,
      countedBinaryMinimumScan_value,countedPlannerFirstChoice,countedPlannerUniformIdentity,
      countedBinaryFilter_value,binaryFirstCoinTest_value,binaryTailCoinTest_value,
      countedPlannerFirstCoins_value,countedPlannerTailCoins_value,countedBinaryPlannerFraction_value,
      BinaryRational.ofRat_value]

end ProphetSecretary.Statistics
