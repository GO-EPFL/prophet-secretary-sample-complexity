import ProphetSecretary.Statistics.FiniteMaximumCDF
import ProphetSecretary.Statistics.EmpiricalPlannerInstance
import ProphetSecretary.Statistics.EmpiricalMaximumVariance
import Mathlib.Data.Rat.Cast.Order

/-!
# Exact empirical maximum computation

The common support contains zero and the positive stored observations.
Marginal distribution functions count every row entry, including repeated
values. The formula computes the expected maximum from polynomially many
marginal counts and products, rather than from the Cartesian product of rows.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n : ℕ} {k : Fin n → ℕ}

section FiniteComputations
variable {Value : Type*} [Field Value] [LinearOrder Value]

def empiricalClosedCDF {m : ℕ} (y : Fin m → Value) (a : Value) : Value :=
  ((Finset.univ.filter (fun j => y j ≤ a)).card : Value) / (m : Value)

def empiricalStrictCDF {m : ℕ} (y : Fin m → Value) (a : Value) : Value :=
  ((Finset.univ.filter (fun j => y j < a)).card : Value) / (m : Value)

def empiricalMaximumSupport (y : (i : Fin n) → Fin (k i) → Value) : Finset Value :=
  insert 0 (Finset.univ.biUnion (fun i =>
    (Finset.univ.filter (fun j => 0 < y i j)).image (y i)))

@[simp] lemma zero_mem_empiricalMaximumSupport (y : (i : Fin n) → Fin (k i) → Value) :
    0 ∈ empiricalMaximumSupport y := Finset.mem_insert_self _ _

lemma positive_mem_empiricalMaximumSupport (y : (i : Fin n) → Fin (k i) → Value)
    (i : Fin n) (j : Fin (k i)) (hy : 0 < y i j) : y i j ∈ empiricalMaximumSupport y := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩⟩

lemma empiricalMaximumSupport_nonnegative (y : (i : Fin n) → Fin (k i) → Value)
    {a : Value} (ha : a ∈ empiricalMaximumSupport y) : 0 ≤ a := by
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact le_rfl
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2.le

lemma max_zero_mem_empiricalMaximumSupport (y : (i : Fin n) → Fin (k i) → Value)
    (i : Fin n) (j : Fin (k i)) : max 0 (y i j) ∈ empiricalMaximumSupport y := by
  by_cases hy : 0 < y i j
  · rw [max_eq_right hy.le]
    exact positive_mem_empiricalMaximumSupport y i j hy
  · rw [max_eq_left (le_of_not_gt hy)]
    exact zero_mem_empiricalMaximumSupport y

def empiricalMaximumValue (y : (i : Fin n) → Fin (k i) → Value) : Value :=
  ∑ a ∈ empiricalMaximumSupport y,
    a * ((∏ i, empiricalClosedCDF (y i) a) - ∏ i, empiricalStrictCDF (y i) a)

lemma empiricalClosedCDF_clamp {m : ℕ} (y : Fin m → Value) {a : Value} (ha : 0 ≤ a) :
    empiricalClosedCDF (fun j => max 0 (y j)) a = empiricalClosedCDF y a := by
  have hSet : (Finset.univ.filter (fun j => max 0 (y j) ≤ a)) =
      (Finset.univ.filter (fun j => y j ≤ a)) := by
    ext j
    simp [ha]
  simp only [empiricalClosedCDF, hSet]

lemma empiricalStrictCDF_clamp {m : ℕ} (y : Fin m → Value) {a : Value} (ha : 0 < a) :
    empiricalStrictCDF (fun j => max 0 (y j)) a = empiricalStrictCDF y a := by
  have hSet : (Finset.univ.filter (fun j => max 0 (y j) < a)) =
      (Finset.univ.filter (fun j => y j < a)) := by
    ext j
    simp [ha]
  simp only [empiricalStrictCDF, hSet]

@[simp] lemma empiricalMaximumValue_empty {k0 : Fin 0 → ℕ}
    (y : (i : Fin 0) → Fin (k0 i) → Value) : empiricalMaximumValue y = 0 := by
  simp [empiricalMaximumValue, empiricalMaximumSupport]

end FiniteComputations

lemma empiricalLaw_closedCDF {m : ℕ} [NeZero m] (y : Fin m → ℝ) (a : ℝ) :
    (empiricalLaw y).real (Iic a) = empiricalClosedCDF y a := by
  have h := integral_empiricalLaw y ((Iic a).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const (1 : ℝ) measurableSet_Iic] at h
  simpa [empiricalClosedCDF, Set.indicator_apply, Finset.sum_boole, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

lemma empiricalLaw_strictCDF {m : ℕ} [NeZero m] (y : Fin m → ℝ) (a : ℝ) :
    (empiricalLaw y).real (Iio a) = empiricalStrictCDF y a := by
  have h := integral_empiricalLaw y ((Iio a).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const (1 : ℝ) measurableSet_Iio] at h
  simpa [empiricalStrictCDF, Set.indicator_apply, Finset.sum_boole, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- The computable formula agrees with the total, nonnegative empirical
instance on every raw array. -/
theorem empiricalMaximumValue_eq_clampedExpectedMaximum [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) :
    empiricalMaximumValue y =
      (empiricalPlannerInstance (fun i j => max 0 (y i j)) (fun _ _ => le_max_left _ _)).expectedMaximum := by
  let P := empiricalPlannerInstance (fun i j => max 0 (y i j)) (fun _ _ => le_max_left _ _)
  have hSupport (i : Fin n) : ∀ᵐ x ∂P.law i, x ∈ empiricalMaximumSupport y := by
    apply Measure.ae_smul_measure
    apply ae_finsetSum_measure_iff.mpr
    intro j _
    simpa using max_zero_mem_empiricalMaximumSupport y i j
  have h := expectedMaximum_eq_CDF_atom_sum P (empiricalMaximumSupport y)
    (zero_mem_empiricalMaximumSupport y) (fun _ ha => empiricalMaximumSupport_nonnegative y ha) hSupport
  rw [h]
  unfold empiricalMaximumValue
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : a = 0
  · subst a
    simp
  · have haPos : 0 < a := lt_of_le_of_ne (empiricalMaximumSupport_nonnegative y ha) (fun h => hz h.symm)
    change a * ((∏ i, empiricalClosedCDF (y i) a) - ∏ i, empiricalStrictCDF (y i) a) =
      a * ((∏ i, (empiricalLaw (fun j => max 0 (y i j))).real (Iic a)) -
        ∏ i, (empiricalLaw (fun j => max 0 (y i j))).real (Iio a))
    simp_rw [empiricalLaw_closedCDF, empiricalLaw_strictCDF,
      empiricalClosedCDF_clamp _ haPos.le, empiricalStrictCDF_clamp _ haPos]

/-- For nonnegative stored data this is exactly the original product-empirical benchmark. -/
theorem empiricalMaximumValue_eq_expectedMaximum [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j) :
    empiricalMaximumValue y = (empiricalPlannerInstance y hy).expectedMaximum := by
  rw [empiricalMaximumValue_eq_clampedExpectedMaximum]
  congr 1
  apply Instance.eq_of_law_eq
  funext i
  change empiricalLaw (fun j => max 0 (y i j)) = empiricalLaw (y i)
  congr 1
  funext j
  exact max_eq_right (hy i j)

/-- Correspondence with the empirical maximum used by the statistical estimates. -/
theorem empiricalMaximumValue_eq_legacy {m : ℕ} [NeZero m] (y : (Fin n × Fin m) → ℝ) :
    empiricalMaximumValue (fun i j => y (i, j)) = empiricalExpectedMaximum y := by
  rw [empiricalMaximumValue_eq_clampedExpectedMaximum]
  unfold empiricalExpectedMaximum
  congr 1

lemma measurable_empiricalMaximumValue {m : ℕ} [NeZero m] :
    Measurable (fun y : (Fin n × Fin m) → ℝ => empiricalMaximumValue (fun i j => y (i, j))) := by
  have he : (fun y : (Fin n × Fin m) → ℝ => empiricalMaximumValue (fun i j => y (i, j))) =
      empiricalExpectedMaximum := by
    funext y
    exact empiricalMaximumValue_eq_legacy y
  rw [he]
  exact measurable_empiricalExpectedMaximum

lemma empiricalClosedCDF_ratCast {m : ℕ} (y : Fin m → ℚ) (a : ℚ) :
    empiricalClosedCDF (fun j => (y j : ℝ)) (a : ℝ) = ((empiricalClosedCDF y a : ℚ) : ℝ) := by
  simp [empiricalClosedCDF]

lemma empiricalStrictCDF_ratCast {m : ℕ} (y : Fin m → ℚ) (a : ℚ) :
    empiricalStrictCDF (fun j => (y j : ℝ)) (a : ℝ) = ((empiricalStrictCDF y a : ℚ) : ℝ) := by
  simp [empiricalStrictCDF]

lemma empiricalMaximumSupport_ratCast (y : (i : Fin n) → Fin (k i) → ℚ) :
    (empiricalMaximumSupport y).image (fun a : ℚ => (a : ℝ)) =
      empiricalMaximumSupport (fun i j => (y i j : ℝ)) := by
  simp only [empiricalMaximumSupport, Finset.image_insert, Rat.cast_zero,
    Finset.biUnion_image, Finset.image_image]
  congr 1
  apply Finset.biUnion_congr rfl
  intro i _
  have hSet : (Finset.univ.filter (fun j => 0 < y i j)) =
      Finset.univ.filter (fun j => (0 : ℝ) < (y i j : ℝ)) := by
    ext j
    simp
  ext a
  simp only [Finset.mem_image, Function.comp_apply, hSet]

/-- The exact rational computation has the same real value. -/
theorem empiricalMaximumValue_ratCast (y : (i : Fin n) → Fin (k i) → ℚ) :
    ((empiricalMaximumValue y : ℚ) : ℝ) = empiricalMaximumValue (fun i j => (y i j : ℝ)) := by
  unfold empiricalMaximumValue
  change (Rat.castHom ℝ) (∑ a ∈ empiricalMaximumSupport y,
    a * ((∏ i, empiricalClosedCDF (y i) a) - ∏ i, empiricalStrictCDF (y i) a)) = _
  rw [map_sum, ← empiricalMaximumSupport_ratCast y, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a _
    change ((a * ((∏ i, empiricalClosedCDF (y i) a) - ∏ i, empiricalStrictCDF (y i) a) : ℚ) : ℝ) = _
    rw [Rat.cast_mul, Rat.cast_sub]
    have hLe : (((∏ i, empiricalClosedCDF (y i) a) : ℚ) : ℝ) =
        ∏ i, empiricalClosedCDF (fun j => (y i j : ℝ)) (a : ℝ) := by
      change (Rat.castHom ℝ) (∏ i, empiricalClosedCDF (y i) a) = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (empiricalClosedCDF_ratCast (y i) a).symm
    have hLt : (((∏ i, empiricalStrictCDF (y i) a) : ℚ) : ℝ) =
        ∏ i, empiricalStrictCDF (fun j => (y i j : ℝ)) (a : ℝ) := by
      change (Rat.castHom ℝ) (∏ i, empiricalStrictCDF (y i) a) = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (empiricalStrictCDF_ratCast (y i) a).symm
    rw [hLe, hLt]
  · intro a _ b _ h
    exact Rat.cast_injective h

end ProphetSecretary.Statistics
