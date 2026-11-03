import ProphetSecretary.Statistics.EmpiricalMaximumWork
import ProphetSecretary.Statistics.EmpiricalPlannerData
import ProphetSecretary.Statistics.PlannerSamplerWork

/-!
# Counted data operations for the scalar planner

The program stores marginal positive probabilities in a vector. Active
lists, product weights, and conditional excesses are computed by counted
scans of stored identities and observations.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

universe u v

variable {n : ℕ} {k : Fin n → ℕ} {Value : Type*}

def plannerStoredRows (y : (i : Fin n) → Fin (k i) → Value) : Vector (List Value) n :=
  Vector.ofFn (fun i => List.ofFn (y i))

@[simp] lemma plannerStoredRows_get (y : (i : Fin n) → Fin (k i) → Value) (i : Fin n) :
    (plannerStoredRows y).get i = List.ofFn (y i) := by
  simp [plannerStoredRows, Vector.get]

def countedPlannerRowProbability [Field Value] [LinearOrder Value] (row : List Value) : Value × ℕ :=
  let q := countedRowCDFCounts row (0 : Value)
  ((q.1.2 - q.1.1.1) / q.1.2, q.2 + 6)

lemma countedPlannerRowProbability_work [Field Value] [LinearOrder Value] (row : List Value) :
    (countedPlannerRowProbability row).2 ≤ 10 * (row.length + 1) := by
  have h := countedRowCDFCounts_work row (0 : Value)
  dsimp only [countedPlannerRowProbability]
  omega

lemma countedPlannerRowProbability_ofFn [Field Value] [LinearOrder Value] {m : ℕ}
    (y : Fin m → Value) :
    (countedPlannerRowProbability (List.ofFn y)).1 = empiricalPositiveProbability y := by
  have hSet : (Finset.univ.filter (fun j => ¬ y j ≤ 0)) = positiveObservations y := by
    ext j
    simp [positiveObservations, not_le]
  have hCard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun j => y j ≤ 0)
  rw [hSet, Finset.card_univ, Fintype.card_fin] at hCard
  have hCast := congrArg (fun x : ℕ => (x : Value)) hCard
  simp only [Nat.cast_add] at hCast
  have hNum : (m : Value) - ((Finset.univ.filter (fun j => y j ≤ 0)).card : Value) =
      ((positiveObservations y).card : Value) := by
    rw [← hCast]
    ring
  simp only [countedPlannerRowProbability, countedRowCDFCounts_value, List.length_ofFn,
    countP_ofFn_eq_card, hNum, empiricalPositiveProbability]

/-- Each row's probability is evaluated once and stored for constant-cost
coordinate access during recursive transitions. -/
def countedPlannerProbabilities [Field Value] [LinearOrder Value] (rows : Vector (List Value) n) :
    Vector (Value × ℕ) n × ℕ :=
  let q := Vector.ofFn (fun i => countedPlannerRowProbability (rows.get i))
  (q, (∑ i : Fin n, (q.get i).2) + 3 * n + 1)

def plannerProbabilityRead (q : Vector (Value × ℕ) n) (i : Fin n) : Value := (q.get i).1

private lemma plannerVectorGet_ofFn {α : Type*} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

lemma countedPlannerProbabilities_ofFn [Field Value] [LinearOrder Value]
    (y : (i : Fin n) → Fin (k i) → Value) (i : Fin n) :
    plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows y)).1 i =
      empiricalPositiveProbability (y i) := by
  simp only [plannerProbabilityRead, countedPlannerProbabilities, plannerVectorGet_ofFn,
    plannerStoredRows_get, countedPlannerRowProbability_ofFn]

lemma countedPlannerProbabilities_work [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (m : ℕ) (hRows : ∀ i, (rows.get i).length ≤ m) :
    (countedPlannerProbabilities rows).2 ≤ 20 * (n + 1) * (m + 1) := by
  have hEach (i : Fin n) : (countedPlannerRowProbability (rows.get i)).2 ≤ 10 * (m + 1) := by
    have hi := hRows i
    exact (countedPlannerRowProbability_work (rows.get i)).trans (by omega)
  have hSum : (∑ i : Fin n, (countedPlannerRowProbability (rows.get i)).2) ≤ n * (10 * (m + 1)) := by
    calc
      _ ≤ ∑ _i : Fin n, 10 * (m + 1) := Finset.sum_le_sum (fun i _ => hEach i)
      _ = _ := by simp
  simp only [countedPlannerProbabilities, plannerVectorGet_ofFn]
  nlinarith [Nat.zero_le (n * m)]

def countedPlannerActive [Field Value] [LinearOrder Value]
    (p : Fin n → Value) : List (Fin n) → List (Fin n) × ℕ
  | [] => ([], 1)
  | i :: l =>
      let q := countedPlannerActive p l
      if 0 < p i then (i :: q.1, q.2 + 5) else (q.1, q.2 + 4)

lemma countedPlannerActive_value [Field Value] [LinearOrder Value]
    (p : Fin n → Value) (l : List (Fin n)) :
    (countedPlannerActive p l).1 = l.filter (fun i => decide (0 < p i)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : 0 < p i <;> simp [countedPlannerActive, hi, ih]

lemma countedPlannerActive_work [Field Value] [LinearOrder Value]
    (p : Fin n → Value) (l : List (Fin n)) : (countedPlannerActive p l).2 ≤ 1 + 5 * l.length := by
  induction l with
  | nil => simp [countedPlannerActive]
  | cons i l ih =>
    unfold countedPlannerActive
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

lemma countedPlannerActive_nodup [Field Value] [LinearOrder Value]
    (p : Fin n → Value) (l : List (Fin n)) (hl : l.Nodup) : (countedPlannerActive p l).1.Nodup := by
  rw [countedPlannerActive_value]
  exact hl.filter _

lemma countedPlannerActive_length [Field Value] [LinearOrder Value]
    (p : Fin n → Value) (l : List (Fin n)) : (countedPlannerActive p l).1.length ≤ l.length := by
  rw [countedPlannerActive_value]
  exact List.length_filter_le _ _

lemma countedPlannerActive_toFinset [Field Value] [LinearOrder Value]
    (p : Fin n → Value) (l : List (Fin n)) :
    (countedPlannerActive p l).1.toFinset = l.toFinset.filter (fun i => 0 < p i) := by
  ext i
  simp [countedPlannerActive_value]

def countedPlannerWeight [Field Value] (p : Fin n → Value) : List (Fin n) → Value × ℕ
  | [] => (1, 1)
  | i :: l =>
      let q := countedPlannerWeight p l
      ((1 + 4 * p i) * q.1, q.2 + 7)

lemma countedPlannerWeight_value [Field Value] (p : Fin n → Value) (l : List (Fin n)) :
    (countedPlannerWeight p l).1 = (l.map (fun i => 1 + 4 * p i)).prod := by
  induction l <;> simp_all [countedPlannerWeight]

lemma countedPlannerWeight_toFinset [Field Value] (p : Fin n → Value) (l : List (Fin n)) (hl : l.Nodup) :
    (countedPlannerWeight p l).1 = ∏ i ∈ l.toFinset, (1 + 4 * p i) := by
  rw [countedPlannerWeight_value, List.prod_toFinset _ hl]

lemma countedPlannerWeight_work [Field Value] (p : Fin n → Value) (l : List (Fin n)) :
    (countedPlannerWeight p l).2 = 1 + 7 * l.length := by
  induction l with
  | nil => simp [countedPlannerWeight]
  | cons i l ih =>
    simp only [countedPlannerWeight, List.length_cons, ih]
    omega

def countedPlannerExcessTotals [Field Value] [LinearOrder Value] (v : Value) :
    List Value → (Value × Value) × ℕ
  | [] => ((0, 0), 2)
  | x :: row =>
      let q := countedPlannerExcessTotals v row
      if 0 < x then ((max 0 (x - v) + q.1.1, q.1.2 + 1), q.2 + 12)
      else (q.1, q.2 + 4)

lemma countedPlannerExcessTotals_value [Field Value] [LinearOrder Value]
    (v : Value) (row : List Value) : (countedPlannerExcessTotals v row).1 =
      ((row.map (fun x => if 0 < x then max 0 (x - v) else 0)).sum,
        (row.countP (fun x => decide (0 < x)) : Value)) := by
  induction row with
  | nil => simp [countedPlannerExcessTotals]
  | cons x row ih =>
    by_cases hx : 0 < x <;> simp [countedPlannerExcessTotals, hx, ih, Nat.cast_add]

lemma countedPlannerExcessTotals_work [Field Value] [LinearOrder Value]
    (v : Value) (row : List Value) : (countedPlannerExcessTotals v row).2 ≤ 2 + 12 * row.length := by
  induction row with
  | nil => simp [countedPlannerExcessTotals]
  | cons x row ih =>
    unfold countedPlannerExcessTotals
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

def countedPlannerExcess [Field Value] [LinearOrder Value] (row : List Value) (v : Value) : Value × ℕ :=
  let q := countedPlannerExcessTotals v row
  (q.1.1 / q.1.2, q.2 + 3)

lemma countedPlannerExcess_ofFn [Field Value] [LinearOrder Value] {m : ℕ}
    (y : Fin m → Value) (v : Value) :
    (countedPlannerExcess (List.ofFn y) v).1 = empiricalConditionalExcess y v := by
  simp only [countedPlannerExcess, countedPlannerExcessTotals_value,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply, countP_ofFn_eq_card,
    empiricalConditionalExcess, positiveObservations, Finset.sum_filter]

lemma countedPlannerExcess_work [Field Value] [LinearOrder Value]
    (row : List Value) (v : Value) : (countedPlannerExcess row v).2 ≤ 5 + 12 * row.length := by
  have h := countedPlannerExcessTotals_work v row
  dsimp only [countedPlannerExcess]
  omega

abbrev ScalarPlannerListState (n : ℕ) (Value : Type*) := List (Fin n) × (Value × Value)

structure ScalarPlannerFrame (n : ℕ) (Value : Type*) where
  active : List (Fin n)
  time : Value
  durationWeight : Value
  weight : Value
  emptyValue : Value
  offset : Value
  coefficient : Value

def countedScalarPlannerFrame [Field Value] [LinearOrder Value] (p : Fin n → Value)
    (x : ScalarPlannerListState n Value) : ScalarPlannerFrame n Value × ℕ :=
  let active := countedPlannerActive p x.1
  let weight := countedPlannerWeight p active.1
  let u := max 0 (min 1 x.2.1)
  let z := max 0 (min 4 x.2.2)
  let wait := z * u
  (⟨active.1, u, z, weight.1, wait, wait / weight.1, (weight.1 - 1) / (4 * weight.1)⟩,
    active.2 + weight.2 + 24)

lemma countedScalarPlannerFrame_active_nodup [Field Value] [LinearOrder Value] (p : Fin n → Value)
    (x : ScalarPlannerListState n Value) (hx : x.1.Nodup) :
    (countedScalarPlannerFrame p x).1.active.Nodup :=
  countedPlannerActive_nodup p x.1 hx

lemma countedScalarPlannerFrame_work [Field Value] [LinearOrder Value] (p : Fin n → Value)
    (x : ScalarPlannerListState n Value) (hx : x.1.Nodup) :
    (countedScalarPlannerFrame p x).2 ≤ 40 * (n + 1) := by
  have hLen := Finset.card_le_univ x.1.toFinset
  rw [List.toFinset_card_of_nodup hx, Fintype.card_fin] at hLen
  have hActive := countedPlannerActive_work p x.1
  have hActiveLen := countedPlannerActive_length p x.1
  dsimp only [countedScalarPlannerFrame]
  rw [countedPlannerWeight_work]
  omega

def countedScalarPlannerChild [Field Value] [LinearOrder Value] (q : ScalarPlannerFrame n Value)
    (o : PlannerListOutput n Value) : ScalarPlannerListState n Value × ℕ :=
  ((o.2.2, (q.time * max 0 (min 1 o.2.1), q.durationWeight)), 10)

def countedScalarPlannerPayoff [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (p : Fin n → Value) (o : PlannerListOutput n Value) (a : Value) :
    Value × ℕ :=
  match o.1 with
  | none => (0, 1)
  | some i =>
      let active := countedPlannerActive p o.2.2
      let weight := countedPlannerWeight p active.1
      let excess := countedPlannerExcess (rows.get i) (weight.1 * a)
      (excess.1 / weight.1, active.2 + weight.2 + excess.2 + 5)

lemma countedScalarPlannerPayoff_work [Field Value] [LinearOrder Value]
    (rows : Vector (List Value) n) (m : ℕ) (hRows : ∀ i, (rows.get i).length ≤ m)
    (p : Fin n → Value) (o : PlannerListOutput n Value) (hO : o.2.2.Nodup) (a : Value) :
    (countedScalarPlannerPayoff rows p o a).2 ≤ 20 * (n + m + 1) := by
  cases hi : o.1 with
  | none =>
    simp only [countedScalarPlannerPayoff, hi]
    omega
  | some i =>
    have hLen := Finset.card_le_univ o.2.2.toFinset
    rw [List.toFinset_card_of_nodup hO, Fintype.card_fin] at hLen
    have hActive := countedPlannerActive_work p o.2.2
    have hActiveLen := countedPlannerActive_length p o.2.2
    have hExcess := countedPlannerExcess_work (rows.get i)
      ((countedPlannerWeight p (countedPlannerActive p o.2.2).1).1 * a)
    have hiRow := hRows i
    simp only [countedScalarPlannerPayoff, hi, countedPlannerWeight_work]
    omega

/-- A full sampler seed is assembled by independent draws into three dense
vectors and two scalar registers. -/
def plannerFullSeedM {M : Type u → Type v} [Monad M] {Value : Type u}
    (n : ℕ) (uniform : M Value) : M (PlannerFieldSeed n Value) := do
  let first ← uniform
  let firstCoins ← Vector.ofFnM (fun _ : Fin n => uniform)
  let identity ← uniform
  let times ← Vector.ofFnM (fun _ : Fin n => uniform)
  let tailCoins ← Vector.ofFnM (fun _ : Fin n => uniform)
  pure ((first, firstCoins.get), (identity, (times.get, tailCoins.get)))

private def countingUniform {Scalar : Type} (a : Scalar) : StateM ℕ Scalar := fun c => (a, c + 1)

private lemma countState_bind {α β : Type} (x : StateM ℕ α) (f : α → StateM ℕ β) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a, s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma countState_pure {α : Type} (a : α) (c : ℕ) :
    (pure a : StateM ℕ α).run c = (a, c) := rfl

private lemma countingUniform_run {Scalar : Type} (a : Scalar) (c : ℕ) : (countingUniform a).run c = (a, c + 1) := rfl

private lemma vectorUniform_draws {Scalar : Type} (a : Scalar) (n c : ℕ) :
    ((Vector.ofFnM (fun _ : Fin n => countingUniform a)).run c).2 = c + n := by
  induction n generalizing c with
  | zero => simp only [Vector.ofFnM_zero, countState_pure, Nat.add_zero]
  | succ n ih =>
    rw [Vector.ofFnM_succ, countState_bind, countState_bind, countingUniform_run, countState_pure]
    change ((Vector.ofFnM (fun _ : Fin n => countingUniform a)).run c).2 + 1 = _
    rw [ih]
    omega

/-- The seed generator makes exactly `3*n+2` calls to its draw primitive. -/
theorem plannerFullSeedM_draws {Scalar : Type} (a : Scalar) (n c : ℕ) :
    ((plannerFullSeedM n (countingUniform a)).run c).2 = c + 3 * n + 2 := by
  simp only [plannerFullSeedM, countState_bind, countingUniform_run, countState_pure, vectorUniform_draws]
  omega

def countedScalarPlannerSample [Field Value] [LinearOrder Value] (p : Fin n → Value)
    (q : ScalarPlannerFrame n Value) (seed : PlannerFieldSeed n Value) : PlannerListOutput n Value × ℕ :=
  let out := countedPlannerUniformSampler q.active p seed
  (out.1, out.2 + 20 * (n + 1))

lemma countedScalarPlannerSample_work [Field Value] [LinearOrder Value] (p : Fin n → Value)
    (q : ScalarPlannerFrame n Value) (hq : q.active.Nodup) (seed : PlannerFieldSeed n Value) :
    (countedScalarPlannerSample p q seed).2 ≤ 1100 * (n + 1) ^ 3 := by
  have h := countedPlannerUniformSampler_work_le_dimension q.active hq p seed
  dsimp only [countedScalarPlannerSample]
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

end ProphetSecretary.Statistics
