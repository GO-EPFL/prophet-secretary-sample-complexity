import ProphetSecretary.Statistics.ScalarPlannerWorkData
import ProphetSecretary.Statistics.ScalarPlannerWorkTree
import ProphetSecretary.Statistics.ScalarPlannerAccuracy

/-!
# The scalar planner's counted list program

Duplicate-free lists represent unseen identities. The program reads stored
rows and precomputed positive probabilities, and interprets sampled child
lists as the finite subsets in the weighted Bellman recursion.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ} {Value : Type*}

def scalarPlannerListInterpret (x : ScalarPlannerListState n ℝ) : ScalarPlannerState n :=
  (x.1.toFinset, x.2)

def countedScalarPlannerRecursion [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (p : Fin n → Value) :
    CountedPlannerRecursion (ScalarPlannerListState n Value) (ScalarPlannerFrame n Value)
      (PlannerFieldSeed n Value) (PlannerListOutput n Value) Value where
  prepare x :=
    let q := countedScalarPlannerFrame p x
    (⟨q.1, q.1.active.isEmpty, q.1.emptyValue, q.1.offset, q.1.coefficient⟩, q.2)
  sample := countedScalarPlannerSample p
  child := countedScalarPlannerChild
  payoff _ := countedScalarPlannerPayoff rows p

def scalarPlannerPrimitiveBound (n m : ℕ) : ℕ := 1200 * (n + 1) ^ 3 + 50 * (n + m + 1)

lemma countedScalarPlannerRecursion_work [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (p : Fin n → Value) (m : ℕ)
    (hRows : ∀ i, (rows.get i).length ≤ m)
    (r : ℕ) (x : ScalarPlannerListState n Value) (hx : x.1.Nodup)
    (t : MultilevelTree (PlannerFieldSeed n Value) r) :
    ((countedScalarPlannerRecursion rows p).estimate r x t).2 ≤
      100 * scalarPlannerPrimitiveBound n m * multilevelTreeWork r t := by
  have hPower : 0 ≤ (n + 1) ^ 3 := Nat.zero_le _
  apply CountedPlannerRecursion.estimate_work _ (fun z : ScalarPlannerListState n Value => z.1.Nodup)
    (scalarPlannerPrimitiveBound n m) (by unfold scalarPlannerPrimitiveBound; omega)
  · intro z hz
    have h := countedScalarPlannerFrame_work p z hz
    change (countedScalarPlannerFrame p z).2 ≤ _
    unfold scalarPlannerPrimitiveBound
    omega
  · intro z hz seed
    have h := countedScalarPlannerSample_work p (countedScalarPlannerFrame p z).1
      (countedScalarPlannerFrame_active_nodup p z hz) seed
    change (countedScalarPlannerSample p (countedScalarPlannerFrame p z).1 seed).2 ≤ _
    unfold scalarPlannerPrimitiveBound
    omega
  · intro z hz seed
    have hN := countedPlannerUniformSampler_nodup (countedScalarPlannerFrame p z).1.active
      (countedScalarPlannerFrame_active_nodup p z hz) p seed
    refine ⟨?_, hN⟩
    change 10 ≤ scalarPlannerPrimitiveBound n m
    unfold scalarPlannerPrimitiveBound
    omega
  · intro z hz seed a
    let o := (countedScalarPlannerSample p (countedScalarPlannerFrame p z).1 seed).1
    have hN : o.2.2.Nodup := countedPlannerUniformSampler_nodup (countedScalarPlannerFrame p z).1.active
      (countedScalarPlannerFrame_active_nodup p z hz) p seed
    have h := countedScalarPlannerPayoff_work rows m hRows p o hN a
    change (countedScalarPlannerPayoff rows p o a).2 ≤ _
    unfold scalarPlannerPrimitiveBound
    omega
  · exact hx

private lemma activeList_interpret (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y) (l : List (Fin n)) :
    (countedPlannerActive p l).1.toFinset = plannerActive y l.toFinset := by
  rw [countedPlannerActive_toFinset, hp]
  rfl

private lemma activeWeight_interpret (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y) (l : List (Fin n)) (hl : l.Nodup) :
    (countedPlannerWeight p (countedPlannerActive p l).1).1 = scalarPlannerWeight y l.toFinset := by
  rw [countedPlannerWeight_toFinset _ _ (countedPlannerActive_nodup p l hl), activeList_interpret y p hp l, hp]
  rfl

lemma countedScalarPlannerFrame_weight (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) :
    (countedScalarPlannerFrame p x).1.weight = scalarPlannerWeight y (scalarPlannerListInterpret x).1 :=
  activeWeight_interpret y p hp x.1 hx

private lemma list_isEmpty_eq_decide_toFinset (l : List (Fin n)) :
    l.isEmpty = decide (l.toFinset = ∅) := by
  cases l <;> simp

lemma countedScalarPlannerFrame_empty (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y) (x : ScalarPlannerListState n ℝ) :
    (countedScalarPlannerFrame p x).1.active.isEmpty = (scalarPlannerRecursion y).isEmpty (scalarPlannerListInterpret x) := by
  change (countedPlannerActive p x.1).1.isEmpty = decide (plannerActive y x.1.toFinset = ∅)
  rw [list_isEmpty_eq_decide_toFinset, activeList_interpret y p hp]

private lemma sample_interpret (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y) (x : ScalarPlannerListState n ℝ)
    (hx : x.1.Nodup) (seed : PlannerUniformSeed n) :
    plannerListOutputToSet (countedScalarPlannerSample p (countedScalarPlannerFrame p x).1 seed).1 =
      (scalarPlannerRecursion y).sample (scalarPlannerListInterpret x) seed := by
  change plannerListOutputToSet (countedPlannerUniformSampler (countedPlannerActive p x.1).1 p seed).1 = _
  rw [countedPlannerUniformSampler_value _ (countedPlannerActive_nodup p x.1 hx),
    activeList_interpret y p hp, hp]
  rfl

private lemma payoff_interpret (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y) (o : PlannerListOutput n ℝ)
    (hO : o.2.2.Nodup) (a : ℝ) :
    (countedScalarPlannerPayoff (plannerStoredRows y) p o a).1 =
      scalarPlannerPayoff y (plannerListOutputToSet o) a := by
  cases hi : o.1 with
  | none => simp [countedScalarPlannerPayoff, scalarPlannerPayoff, plannerListOutputToSet, hi]
  | some i =>
    simp only [countedScalarPlannerPayoff, scalarPlannerPayoff, plannerListOutputToSet, hi,
      plannerStoredRows_get, countedPlannerExcess_ofFn, activeWeight_interpret y p hp o.2.2 hO]

/-- The stored-row list evaluator agrees pointwise with the semantic
weighted empirical estimate, on every raw seed tree. -/
theorem countedScalarPlannerEstimate_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y)
    (r : ℕ) (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup)
    (t : MultilevelTree (PlannerUniformSeed n) r) :
    ((countedScalarPlannerRecursion (plannerStoredRows y) p).estimate r x t).1 =
      multilevelEstimate (scalarPlannerRecursion y) r (scalarPlannerListInterpret x) t := by
  rw [CountedPlannerRecursion.estimate_value]
  apply multilevelEstimate_transport _ _ scalarPlannerListInterpret (fun z : ScalarPlannerListState n ℝ => z.1.Nodup)
  · intro z _
    exact countedScalarPlannerFrame_empty y p hp z
  · intro z _
    rfl
  · intro z hz
    change (scalarPlannerDurationWeight (scalarPlannerListInterpret z) * scalarPlannerTime (scalarPlannerListInterpret z)) /
        (countedScalarPlannerFrame p z).1.weight = _
    rw [countedScalarPlannerFrame_weight y p hp z hz]
    rfl
  · intro z hz
    change ((countedScalarPlannerFrame p z).1.weight - 1) / (4 * (countedScalarPlannerFrame p z).1.weight) = _
    rw [countedScalarPlannerFrame_weight y p hp z hz]
    rfl
  · intro z hz seed
    rw [← sample_interpret y p hp z hz seed]
    rfl
  · intro z hz seed
    exact countedPlannerUniformSampler_nodup (countedScalarPlannerFrame p z).1.active
      (countedScalarPlannerFrame_active_nodup p z hz) p seed
  · intro z hz seed a
    rw [← sample_interpret y p hp z hz seed]
    exact payoff_interpret y p hp _
      (countedPlannerUniformSampler_nodup (countedScalarPlannerFrame p z).1.active
        (countedScalarPlannerFrame_active_nodup p z hz) p seed) a
  · exact hx

def countedScalarPlannerSinglePrepared [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (p : Fin n → Value) (β : Value)
    (x : ScalarPlannerListState n Value) (r : ℕ) (t : MultilevelTree (PlannerFieldSeed n Value) r) :
    Value × ℕ :=
  let w := (countedScalarPlannerRecursion rows p).estimate r x t
  (β * w.1, w.2 + 3)

lemma countedScalarPlannerSinglePrepared_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (p : Fin n → ℝ) (hp : p = plannerPositiveProbability y) (β : ℝ)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup)
    (hβ : β = scalarPlannerWeight y (scalarPlannerListInterpret x).1)
    (r : ℕ) (t : MultilevelTree (PlannerUniformSeed n) r) :
    (countedScalarPlannerSinglePrepared (plannerStoredRows y) p β x r t).1 =
      (scalarPlannerSingle y (scalarPlannerListInterpret x) r t).1 := by
  simp only [countedScalarPlannerSinglePrepared, hβ, countedScalarPlannerEstimate_value y p hp r x hx t,
    scalarPlannerSingle]

lemma countedScalarPlannerSinglePrepared_work [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (p : Fin n → Value) (β : Value) (m : ℕ)
    (hRows : ∀ i, (rows.get i).length ≤ m)
    (x : ScalarPlannerListState n Value) (hx : x.1.Nodup)
    (r : ℕ) (t : MultilevelTree (PlannerFieldSeed n Value) r) :
    (countedScalarPlannerSinglePrepared rows p β x r t).2 ≤
      400 * scalarPlannerPrimitiveBound n m * 16 ^ r + 3 := by
  have hUnits : multilevelTreeWork r t ≤ 4 * 16 ^ r := by exact_mod_cast multilevelTreeWork_le r t
  have h := countedScalarPlannerRecursion_work rows p m hRows r x hx t
  have hMul := Nat.mul_le_mul_left (100 * scalarPlannerPrimitiveBound n m) hUnits
  calc
    _ ≤ (100 * scalarPlannerPrimitiveBound n m) * (4 * 16 ^ r) + 3 :=
      Nat.add_le_add_right (h.trans hMul) _
    _ = _ := by ring

/-- All copies read the same stored probabilities and root weight. -/
def countedScalarPlannerQueryAtLevel [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]
    (rows : Vector (List Value) n) (x : ScalarPlannerListState n Value) (r : ℕ)
    (pFail : Value) (H : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ pFail)
    (seed : Fin (confidenceCopyCount pFail H) → MultilevelTree (PlannerFieldSeed n Value) r) :
    MedianCopiesResult Value :=
  let prepared := countedPlannerProbabilities rows
  let p := plannerProbabilityRead prepared.1
  let frame := countedScalarPlannerFrame p x
  if frame.1.active.isEmpty then
    { value := frame.1.emptyValue, work := prepared.2 + frame.2 + 2, copies := 0 }
  else
    let q := confidenceMedianCopies pFail H (countedScalarPlannerSinglePrepared rows p frame.1.weight x r) seed
    { value := clipFive q.value, work := prepared.2 + frame.2 + q.work + 5, copies := q.copies }

/-- The arithmetic query returns the same estimate as the confidence-
amplified scalar planner, including the exact empty-state return. -/
theorem countedScalarPlannerQueryAtLevel_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) (r : ℕ)
    (pFail : ℝ) (H : ∃ j : ℕ, (1 / 4 : ℝ) ^ j ≤ pFail)
    (seed : Fin (confidenceCopyCount pFail H) → MultilevelTree (PlannerUniformSeed n) r) :
    (countedScalarPlannerQueryAtLevel (plannerStoredRows y) x r pFail H seed).value =
      (scalarPlannerQueryAtLevel y (scalarPlannerListInterpret x) r pFail H seed).value := by
  let prepared := countedPlannerProbabilities (plannerStoredRows y)
  let p := plannerProbabilityRead prepared.1
  let frame := countedScalarPlannerFrame p x
  have hp : p = plannerPositiveProbability y := by
    funext i
    exact countedPlannerProbabilities_ofFn y i
  have hFlag : frame.1.active.isEmpty =
      (scalarPlannerRecursion y).isEmpty (scalarPlannerListInterpret x) :=
    countedScalarPlannerFrame_empty y p hp x
  have hβ : frame.1.weight = scalarPlannerWeight y (scalarPlannerListInterpret x).1 :=
    countedScalarPlannerFrame_weight y p hp x hx
  have hCall (t : MultilevelTree (PlannerUniformSeed n) r) :
      (countedScalarPlannerSinglePrepared (plannerStoredRows y) p frame.1.weight x r t).1 =
        (scalarPlannerSingle y (scalarPlannerListInterpret x) r t).1 :=
    countedScalarPlannerSinglePrepared_value y p hp frame.1.weight x hx hβ r t
  unfold countedScalarPlannerQueryAtLevel scalarPlannerQueryAtLevel
  dsimp only
  by_cases he : frame.1.active.isEmpty = true
  · have he' : (scalarPlannerRecursion y).isEmpty (scalarPlannerListInterpret x) = true := hFlag.symm.trans he
    change (if frame.1.active.isEmpty then _ else _ : MedianCopiesResult ℝ).value = _
    simp only [he, he', if_true]
    rfl
  · have he' : ¬ (scalarPlannerRecursion y).isEmpty (scalarPlannerListInterpret x) = true :=
      fun h => he (hFlag.trans h)
    change (if frame.1.active.isEmpty then _ else _ : MedianCopiesResult ℝ).value = _
    simp only [if_neg he, if_neg he', confidenceMedianCopies_value]
    apply congrArg clipFive
    apply congrArg (sortedMedian (countedConfidenceLevel pFail H).1)
    funext i
    exact hCall (seed i)

/-- Arithmetic and random-read work for the actual confidence query. The
bound holds on every supplied raw seed family. -/
theorem countedScalarPlannerQueryAtLevel_work [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]
    (rows : Vector (List Value) n) (m : ℕ) (hRows : ∀ i, (rows.get i).length ≤ m)
    (x : ScalarPlannerListState n Value) (hx : x.1.Nodup) (r : ℕ)
    (pFail : Value) (H : ∃ j : ℕ, (1 / 4 : Value) ^ j ≤ pFail)
    (seed : Fin (confidenceCopyCount pFail H) → MultilevelTree (PlannerFieldSeed n Value) r) :
    (countedScalarPlannerQueryAtLevel rows x r pFail H seed).work ≤
      20 * (n + 1) * (m + 1) + 40 * (n + 1) +
        confidenceCopyCount pFail H * (400 * scalarPlannerPrimitiveBound n m * 16 ^ r + 3) +
          10 * (confidenceCopyCount pFail H + 1) ^ 2 + 5 := by
  let prepared := countedPlannerProbabilities rows
  let p := plannerProbabilityRead prepared.1
  let frame := countedScalarPlannerFrame p x
  let call := countedScalarPlannerSinglePrepared rows p frame.1.weight x r
  have hPrep : prepared.2 ≤ 20 * (n + 1) * (m + 1) := countedPlannerProbabilities_work rows m hRows
  have hFrame : frame.2 ≤ 40 * (n + 1) := countedScalarPlannerFrame_work p x hx
  have hMedian := confidenceMedianCopies_work pFail H call seed
    (400 * scalarPlannerPrimitiveBound n m * 16 ^ r + 3)
    (fun t => countedScalarPlannerSinglePrepared_work rows p frame.1.weight m hRows x hx r t)
  unfold countedScalarPlannerQueryAtLevel
  dsimp only
  by_cases he : frame.1.active.isEmpty = true
  · change (if frame.1.active.isEmpty then _ else _ : MedianCopiesResult Value).work ≤ _
    rw [if_pos he]
    change prepared.2 + frame.2 + 2 ≤ _
    omega
  · change (if frame.1.active.isEmpty then _ else _ : MedianCopiesResult Value).work ≤ _
    rw [if_neg he]
    change prepared.2 + frame.2 + (confidenceMedianCopies pFail H call seed).work + 5 ≤ _
    omega

/-- The counted program has the confidence guarantee of the weighted
recursion, and the hard work bound of its actual arithmetic operations. -/
theorem countedScalarPlannerQueryAtLevel_correct [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1)
    (m : ℕ) (hk : ∀ i, k i ≤ m) (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup)
    (r : ℕ) (h pFail : ℝ) (hh : 0 < h) (hp : 0 < pFail) (hp1 : pFail < 1)
    (H : ∃ j : ℕ, (1 / 4 : ℝ) ^ j ≤ pFail)
    (hprec : 25 * (scalarPlannerWeight y (scalarPlannerListInterpret x).1) ^ 2 * (1 / 2 : ℝ) ^ r ≤ h ^ 2 / 64) :
    let C := confidenceCopyCount pFail H
    let call := countedScalarPlannerQueryAtLevel (plannerStoredRows y) x r pFail H
    Measurable (fun seed => (call seed).value) ∧
      (Measure.pi (fun _ : Fin C => multilevelTreeLaw (plannerUniformSeedLaw n) r)).real
        {seed | h < |(call seed).value - scalarPlannerValue y hy (scalarPlannerListInterpret x)|} ≤ pFail ∧
      ∀ seed, (call seed).work ≤
        20 * (n + 1) * (m + 1) + 40 * (n + 1) +
          C * (400 * scalarPlannerPrimitiveBound n m * 16 ^ r + 3) + 10 * (C + 1) ^ 2 + 5 := by
  dsimp only
  have hc := scalarPlannerQueryAtLevel_correct y hy hcap (scalarPlannerListInterpret x) r h pFail hh hp hp1 H hprec
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [countedScalarPlannerQueryAtLevel_value y x hx r pFail H]
    exact hc.1
  · simp_rw [countedScalarPlannerQueryAtLevel_value y x hx r pFail H]
    exact hc.2.1
  · intro seed
    exact countedScalarPlannerQueryAtLevel_work (plannerStoredRows y) m
      (fun i => by simpa using hk i) x hx r pFail H seed

end ProphetSecretary.Statistics
