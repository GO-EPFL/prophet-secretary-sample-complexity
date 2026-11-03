import ProphetSecretary.Statistics.EmpiricalMaximumComputation
import ProphetSecretary.Statistics.PlannerSamplerPhases
import ProphetSecretary.Probability.CountedMedian
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counted exact computation of the product-empirical maximum

The algorithm forms distinct positive support values once. At each support
value it scans every stored row and multiplies the two marginal CDF values.
Repeated observations remain in the row scans. Work is polynomial in the
number of rows and the total number of stored observations.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {Value : Type*}

def countedDistinct [DecidableEq Value] (l : List Value) : List Value × ℕ :=
  match l with
  | [] => ([], 1)
  | a :: l =>
      let tail := countedDistinct l
      let membership := countedListContains a tail.1
      if membership.1 then (tail.1, tail.2 + membership.2 + 1)
      else (a :: tail.1, tail.2 + membership.2 + 2)

lemma countedDistinct_nodup [DecidableEq Value] (l : List Value) : (countedDistinct l).1.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    by_cases ha : a ∈ (countedDistinct l).1
    · simpa [countedDistinct, countedListContains_value, ha] using ih
    · simpa [countedDistinct, countedListContains_value, ha] using List.nodup_cons.mpr ⟨ha, ih⟩

lemma countedDistinct_mem [DecidableEq Value] (l : List Value) (a : Value) : a ∈ (countedDistinct l).1 ↔ a ∈ l := by
  induction l generalizing a with
  | nil => simp [countedDistinct]
  | cons b l ih =>
    by_cases hb : b ∈ (countedDistinct l).1
    · have hb' := (ih b).mp hb
      by_cases hEq : a = b
      · subst a
        simp [countedDistinct, countedListContains_value, hb, hb']
      · simp [countedDistinct, countedListContains_value, hb, ih, hEq]
    · simp [countedDistinct, countedListContains_value, hb, ih]

lemma countedDistinct_length [DecidableEq Value] (l : List Value) : (countedDistinct l).1.length ≤ l.length := by
  induction l with
  | nil => simp [countedDistinct]
  | cons a l ih =>
    unfold countedDistinct
    dsimp only
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

lemma countedDistinct_work [DecidableEq Value] (l : List Value) : (countedDistinct l).2 ≤ 4 * (l.length + 1) ^ 2 := by
  induction l with
  | nil => norm_num [countedDistinct]
  | cons a l ih =>
    have hm := countedListContains_work a (countedDistinct l).1
    have hLen := countedDistinct_length l
    unfold countedDistinct
    dsimp only
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> nlinarith

/-- Closed count, strict count, and row length, all accumulated in the field. -/
def countedRowCDFCounts [Field Value] [LinearOrder Value] (row : List Value) (a : Value) : ((Value × Value) × Value) × ℕ :=
  match row with
  | [] => (((0, 0), 0), 3)
  | x :: row =>
      let tail := countedRowCDFCounts row a
      let len := tail.1.2 + 1
      if x < a then (((tail.1.1.1 + 1, tail.1.1.2 + 1), len), tail.2 + 9)
      else if x ≤ a then (((tail.1.1.1 + 1, tail.1.1.2), len), tail.2 + 8)
      else (((tail.1.1.1, tail.1.1.2), len), tail.2 + 6)

lemma countedRowCDFCounts_value [Field Value] [LinearOrder Value] (row : List Value) (a : Value) :
    (countedRowCDFCounts row a).1 =
      (((row.countP (fun x => decide (x ≤ a)) : Value),
        (row.countP (fun x => decide (x < a)) : Value)), (row.length : Value)) := by
  induction row with
  | nil => simp [countedRowCDFCounts]
  | cons x row ih =>
    by_cases hlt : x < a
    · have hle := hlt.le
      simp [countedRowCDFCounts, hlt, hle, ih, Nat.cast_add]
    · by_cases hle : x ≤ a <;> simp [countedRowCDFCounts, hlt, hle, ih, Nat.cast_add]

lemma countedRowCDFCounts_work [Field Value] [LinearOrder Value] (row : List Value) (a : Value) :
    (countedRowCDFCounts row a).2 ≤ 3 + 9 * row.length := by
  induction row with
  | nil => simp [countedRowCDFCounts]
  | cons x row ih =>
    unfold countedRowCDFCounts
    dsimp only
    split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

def countedRowCDF [Field Value] [LinearOrder Value] (row : List Value) (a : Value) : (Value × Value) × ℕ :=
  let q := countedRowCDFCounts row a
  ((q.1.1.1 / q.1.2, q.1.1.2 / q.1.2), q.2 + 6)

lemma countedRowCDF_value [Field Value] [LinearOrder Value] (row : List Value) (a : Value) :
    (countedRowCDF row a).1 =
      ((row.countP (fun x => decide (x ≤ a)) : Value) / (row.length : Value),
        (row.countP (fun x => decide (x < a)) : Value) / (row.length : Value)) := by
  simp only [countedRowCDF, countedRowCDFCounts_value]

lemma countedRowCDF_work [Field Value] [LinearOrder Value] (row : List Value) (a : Value) :
    (countedRowCDF row a).2 ≤ 10 * (row.length + 1) := by
  have h := countedRowCDFCounts_work row a
  dsimp only [countedRowCDF]
  omega

def countedCDFProducts [Field Value] [LinearOrder Value] (rows : List (List Value)) (a : Value) : (Value × Value) × ℕ :=
  match rows with
  | [] => ((1, 1), 2)
  | row :: rows =>
      let head := countedRowCDF row a
      let tail := countedCDFProducts rows a
      ((head.1.1 * tail.1.1, head.1.2 * tail.1.2), head.2 + tail.2 + 3)

lemma countedCDFProducts_value [Field Value] [LinearOrder Value] (rows : List (List Value)) (a : Value) :
    (countedCDFProducts rows a).1 =
      ((rows.map (fun row => (row.countP (fun x => decide (x ≤ a)) : Value) / (row.length : Value))).prod,
        (rows.map (fun row => (row.countP (fun x => decide (x < a)) : Value) / (row.length : Value))).prod) := by
  induction rows <;> simp_all [countedCDFProducts, countedRowCDF_value]

lemma countedCDFProducts_work [Field Value] [LinearOrder Value] (rows : List (List Value)) (a : Value) :
    (countedCDFProducts rows a).2 ≤ 20 * (rows.length + rows.flatten.length + 1) := by
  induction rows with
  | nil => norm_num [countedCDFProducts]
  | cons row rows ih =>
    have h := countedRowCDF_work row a
    dsimp only [countedCDFProducts]
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

def countedFlattenRows (rows : List (List Value)) : List Value × ℕ :=
  match rows with
  | [] => ([], 1)
  | row :: rows =>
      let tail := countedFlattenRows rows
      let q := countedAppend row tail.1
      (q.1, tail.2 + q.2 + 1)

lemma countedFlattenRows_value (rows : List (List Value)) : (countedFlattenRows rows).1 = rows.flatten := by
  induction rows <;> simp_all [countedFlattenRows, countedAppend_value]

lemma countedFlattenRows_work (rows : List (List Value)) :
    (countedFlattenRows rows).2 ≤ 1 + 2 * rows.length + 2 * rows.flatten.length := by
  induction rows with
  | nil => simp [countedFlattenRows]
  | cons row rows ih =>
    dsimp only [countedFlattenRows]
    rw [countedAppend_work]
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

def countedEmpiricalSupport [Field Value] [LinearOrder Value] (rows : List (List Value)) : List Value × ℕ :=
  let flat := countedFlattenRows rows
  let positives := countedPredicateFilter (fun a => 0 < a) flat.1
  let q := countedDistinct (0 :: positives.1)
  (q.1, flat.2 + positives.2 + q.2 + 2)

lemma countedEmpiricalSupport_nodup [Field Value] [LinearOrder Value] (rows : List (List Value)) : (countedEmpiricalSupport rows).1.Nodup :=
  countedDistinct_nodup _

lemma countedEmpiricalSupport_mem [Field Value] [LinearOrder Value] (rows : List (List Value)) (a : Value) :
    a ∈ (countedEmpiricalSupport rows).1 ↔ a = 0 ∨ (a ∈ rows.flatten ∧ 0 < a) := by
  simp [countedEmpiricalSupport, countedDistinct_mem, countedPredicateFilter_value, countedFlattenRows_value]
  constructor
  · rintro (hz | ⟨row, hr, ha, hPos⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨⟨row, hr, ha⟩, hPos⟩
  · rintro (hz | ⟨⟨row, hr, ha⟩, hPos⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨row, hr, ha, hPos⟩

lemma countedEmpiricalSupport_length [Field Value] [LinearOrder Value] (rows : List (List Value)) :
    (countedEmpiricalSupport rows).1.length ≤ rows.flatten.length + 1 := by
  have h := countedDistinct_length (0 :: (countedPredicateFilter (fun a => 0 < a) (countedFlattenRows rows).1).1)
  have hPos : (countedPredicateFilter (fun a => 0 < a) (countedFlattenRows rows).1).1.length ≤
      rows.flatten.length := by
    rw [countedPredicateFilter_value, countedFlattenRows_value]
    exact List.length_filter_le _ _
  dsimp only [countedEmpiricalSupport]
  simp only [List.length_cons] at h
  omega

def countedEmpiricalAtoms [Field Value] [LinearOrder Value] (support : List Value) (rows : List (List Value)) : Value × ℕ :=
  match support with
  | [] => (0, 1)
  | a :: support =>
      let head := countedCDFProducts rows a
      let tail := countedEmpiricalAtoms support rows
      (a * (head.1.1 - head.1.2) + tail.1, head.2 + tail.2 + 5)

lemma countedEmpiricalAtoms_value [Field Value] [LinearOrder Value] (support : List Value) (rows : List (List Value)) :
    (countedEmpiricalAtoms support rows).1 =
      (support.map (fun a => a * ((countedCDFProducts rows a).1.1 - (countedCDFProducts rows a).1.2))).sum := by
  induction support <;> simp_all [countedEmpiricalAtoms]

lemma countedEmpiricalAtoms_work [Field Value] [LinearOrder Value] (support : List Value) (rows : List (List Value)) :
    (countedEmpiricalAtoms support rows).2 ≤
      1 + support.length * (20 * (rows.length + rows.flatten.length + 1) + 5) := by
  induction support with
  | nil => simp [countedEmpiricalAtoms]
  | cons a support ih =>
    have h := countedCDFProducts_work rows a
    dsimp only [countedEmpiricalAtoms]
    simp only [List.length_cons]
    nlinarith

def countedEmpiricalMaximum [Field Value] [LinearOrder Value] (rows : List (List Value)) : Value × ℕ :=
  let support := countedEmpiricalSupport rows
  let q := countedEmpiricalAtoms support.1 rows
  (q.1, support.2 + q.2 + 1)

lemma countedEmpiricalSupport_work [Field Value] [LinearOrder Value] (rows : List (List Value)) :
    (countedEmpiricalSupport rows).2 ≤
      4 * (rows.flatten.length + 2) ^ 2 + 2 * rows.length + 5 * rows.flatten.length + 4 := by
  let flat := countedFlattenRows rows
  let positives := countedPredicateFilter (fun a => (0 : Value) < a) flat.1
  have hFlat := countedFlattenRows_work rows
  have hPos : positives.2 ≤ 1 + 3 * rows.flatten.length := by
    calc
      positives.2 ≤ 1 + 3 * flat.1.length := countedPredicateFilter_work (fun a => (0 : Value) < a) flat.1
      _ = _ := by rw [countedFlattenRows_value]
  have hPosLen : positives.1.length ≤ rows.flatten.length := by
    rw [countedPredicateFilter_value, countedFlattenRows_value]
    exact List.length_filter_le _ _
  have hDistinct := countedDistinct_work (0 :: positives.1)
  have hSquare : ((0 :: positives.1).length + 1) ^ 2 ≤ (rows.flatten.length + 2) ^ 2 :=
    Nat.pow_le_pow_left (by simp only [List.length_cons]; omega) 2
  have hDistinct' := hDistinct.trans (Nat.mul_le_mul_left 4 hSquare)
  change flat.2 + positives.2 + (countedDistinct (0 :: positives.1)).2 + 2 ≤ _
  nlinarith

/-- A hard quadratic bound in rows plus total stored observations. -/
theorem countedEmpiricalMaximum_work [Field Value] [LinearOrder Value] (rows : List (List Value)) :
    (countedEmpiricalMaximum rows).2 ≤ 100 * (rows.length + rows.flatten.length + 1) ^ 2 := by
  let support := countedEmpiricalSupport rows
  have hSupport := countedEmpiricalSupport_work rows
  have hAtoms := countedEmpiricalAtoms_work support.1 rows
  have hLen := countedEmpiricalSupport_length rows
  have hMul := Nat.mul_le_mul_right (20 * (rows.length + rows.flatten.length + 1) + 5) hLen
  change support.2 + (countedEmpiricalAtoms support.1 rows).2 + 1 ≤ _
  nlinarith [Nat.zero_le (rows.length ^ 2), Nat.zero_le (rows.flatten.length ^ 2),
    Nat.zero_le (rows.length * rows.flatten.length)]

def empiricalStoredRows {n : ℕ} {k : Fin n → ℕ} (y : (i : Fin n) → Fin (k i) → Value) : List (List Value) :=
  List.ofFn (fun i => List.ofFn (y i))

@[simp] lemma empiricalStoredRows_length {n : ℕ} {k : Fin n → ℕ}
    (y : (i : Fin n) → Fin (k i) → Value) : (empiricalStoredRows y).length = n := by
  simp [empiricalStoredRows]

@[simp] lemma empiricalStoredRows_flatten_length {n : ℕ} {k : Fin n → ℕ}
    (y : (i : Fin n) → Fin (k i) → Value) : (empiricalStoredRows y).flatten.length = ∑ i, k i := by
  simp only [empiricalStoredRows, List.length_flatten, List.map_ofFn, Function.comp_apply,
    List.length_ofFn, List.sum_ofFn]

lemma countedRowCDF_ofFn [Field Value] [LinearOrder Value] {m : ℕ}
    (y : Fin m → Value) (a : Value) :
    (countedRowCDF (List.ofFn y) a).1 = (empiricalClosedCDF y a, empiricalStrictCDF y a) := by
  rw [countedRowCDF_value, List.length_ofFn,
    countP_ofFn_eq_card y (fun x => x ≤ a), countP_ofFn_eq_card y (fun x => x < a)]
  rfl

lemma countedCDFProducts_ofFn [Field Value] [LinearOrder Value] {n : ℕ} {k : Fin n → ℕ}
    (y : (i : Fin n) → Fin (k i) → Value) (a : Value) :
    (countedCDFProducts (empiricalStoredRows y) a).1 =
      (∏ i, empiricalClosedCDF (y i) a, ∏ i, empiricalStrictCDF (y i) a) := by
  rw [countedCDFProducts_value]
  simp only [empiricalStoredRows, List.map_ofFn, List.prod_ofFn, Function.comp_apply, List.length_ofFn]
  apply Prod.ext <;> dsimp only
  · apply Finset.prod_congr rfl
    intro i _
    rw [countP_ofFn_eq_card (y i) (fun x => x ≤ a)]
    rfl
  · apply Finset.prod_congr rfl
    intro i _
    rw [countP_ofFn_eq_card (y i) (fun x => x < a)]
    rfl

lemma countedEmpiricalSupport_ofFn [Field Value] [LinearOrder Value] {n : ℕ} {k : Fin n → ℕ}
    (y : (i : Fin n) → Fin (k i) → Value) :
    (countedEmpiricalSupport (empiricalStoredRows y)).1.toFinset = empiricalMaximumSupport y := by
  ext a
  constructor
  · intro ha
    rcases (countedEmpiricalSupport_mem _ a).mp (List.mem_toFinset.mp ha) with hz | ⟨ha, hPos⟩
    · subst a
      exact zero_mem_empiricalMaximumSupport y
    · obtain ⟨row, hRow, haRow⟩ := List.mem_flatten.mp ha
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hRow
      subst row
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp haRow
      rw [← hj]
      exact positive_mem_empiricalMaximumSupport y i j (by rwa [hj])
  · intro ha
    apply List.mem_toFinset.mpr
    apply (countedEmpiricalSupport_mem _ a).mpr
    rcases Finset.mem_insert.mp ha with hz | ha
    · exact Or.inl hz
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      refine Or.inr ⟨List.mem_flatten.mpr ⟨List.ofFn (y i), ?_, ?_⟩, ?_⟩
      · exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · exact List.mem_ofFn.mpr ⟨j, he⟩
      · rw [← he]
        exact (Finset.mem_filter.mp hj).2

/-- The counted stored-row algorithm is the exact finite CDF formula. -/
theorem countedEmpiricalMaximum_value [Field Value] [LinearOrder Value] {n : ℕ} {k : Fin n → ℕ}
    (y : (i : Fin n) → Fin (k i) → Value) :
    (countedEmpiricalMaximum (empiricalStoredRows y)).1 = empiricalMaximumValue y := by
  change (countedEmpiricalAtoms (countedEmpiricalSupport (empiricalStoredRows y)).1
    (empiricalStoredRows y)).1 = _
  rw [countedEmpiricalAtoms_value]
  rw [← List.sum_toFinset _ (countedEmpiricalSupport_nodup (empiricalStoredRows y)),
    countedEmpiricalSupport_ofFn]
  unfold empiricalMaximumValue
  apply Finset.sum_congr rfl
  intro a _
  rw [countedCDFProducts_ofFn]

/-- Explicit polynomial bound when each row contains at most `m` observations. -/
theorem countedEmpiricalMaximum_work_le_rows [Field Value] [LinearOrder Value]
    {n m : ℕ} {k : Fin n → ℕ} (y : (i : Fin n) → Fin (k i) → Value) (hk : ∀ i, k i ≤ m) :
    (countedEmpiricalMaximum (empiricalStoredRows y)).2 ≤ 100 * (n + 1) ^ 2 * (m + 1) ^ 2 := by
  have h := countedEmpiricalMaximum_work (empiricalStoredRows y)
  rw [empiricalStoredRows_length, empiricalStoredRows_flatten_length] at h
  have hSum : ∑ i, k i ≤ n * m := by
    calc
      ∑ i, k i ≤ ∑ _i : Fin n, m := Finset.sum_le_sum (fun i _ => hk i)
      _ = n * m := by simp
  have hSize : n + (∑ i, k i) + 1 ≤ (n + 1) * (m + 1) := by nlinarith
  calc
    _ ≤ 100 * (n + (∑ i, k i) + 1) ^ 2 := h
    _ ≤ 100 * ((n + 1) * (m + 1)) ^ 2 := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hSize 2)
    _ = _ := by ring

/-- On every raw real training array, the computed value is the totalized
empirical maximum used by the statistical analysis. -/
theorem countedEmpiricalMaximum_eq_legacy {n m : ℕ} [NeZero m] (y : (Fin n × Fin m) → ℝ) :
    (countedEmpiricalMaximum (empiricalStoredRows (fun i j => y (i, j)))).1 =
      ProphetSecretary.Model.empiricalExpectedMaximum y := by
  rw [countedEmpiricalMaximum_value, empiricalMaximumValue_eq_legacy]

/-- The heterogeneous-row program also realizes the expected maximum for
nonnegative stored values. -/
theorem countedEmpiricalMaximum_eq_expectedMaximum {n : ℕ} {k : Fin n → ℕ} [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j) :
    (countedEmpiricalMaximum (empiricalStoredRows y)).1 =
      (empiricalPlannerInstance y hy).expectedMaximum := by
  rw [countedEmpiricalMaximum_value, empiricalMaximumValue_eq_expectedMaximum y hy]

/-- Exact rational evaluation gives the real empirical maximum computation. -/
theorem countedEmpiricalMaximum_ratCast {n : ℕ} {k : Fin n → ℕ}
    (y : (i : Fin n) → Fin (k i) → ℚ) :
    (((countedEmpiricalMaximum (empiricalStoredRows y)).1 : ℚ) : ℝ) =
      (countedEmpiricalMaximum (empiricalStoredRows (fun i j => (y i j : ℝ)))).1 := by
  simp only [countedEmpiricalMaximum_value, empiricalMaximumValue_ratCast]

lemma measurable_countedEmpiricalMaximum {n m : ℕ} [NeZero m] :
    Measurable (fun y : (Fin n × Fin m) → ℝ =>
      (countedEmpiricalMaximum (empiricalStoredRows (fun i j => y (i, j)))).1) := by
  have he : (fun y : (Fin n × Fin m) → ℝ =>
      (countedEmpiricalMaximum (empiricalStoredRows (fun i j => y (i, j)))).1) =
      ProphetSecretary.Model.empiricalExpectedMaximum := by
    funext y
    exact countedEmpiricalMaximum_eq_legacy y
  rw [he]
  exact ProphetSecretary.Model.measurable_empiricalExpectedMaximum

end ProphetSecretary.Statistics
