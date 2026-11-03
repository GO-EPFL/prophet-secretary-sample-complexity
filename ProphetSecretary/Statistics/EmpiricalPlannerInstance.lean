import ProphetSecretary.Statistics.EmpiricalPlannerLaw
import ProphetSecretary.Model.ZeroAppendContinuation
import ProphetSecretary.Model.ScalarCoefficientMeasurability
import ProphetSecretary.Statistics.PlannerWeights

/-!
# Empirical instances and active identities for scalar planning

Rows may have different positive lengths. Known empirical zero variables
are removed only from continuation computations; online observation histories
still retain their identities. Removing them preserves the full scalar value
by the proved causal zero simulation.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n : ℕ} {k : Fin n → ℕ} [∀ i, NeZero (k i)]

noncomputable def empiricalPlannerInstance (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) : Instance n where
  law i := empiricalLaw (y i)
  probability _ := inferInstance
  nonnegative i := empiricalLaw_nonnegative (y i) (hy i)

lemma empiricalPlannerInstance_integrable (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) :
    Integrable Instance.maximum (empiricalPlannerInstance y hy).valuesLaw := by
  apply Instance.integrable_maximum
  intro i
  exact integrable_empiricalLaw (y i) id

lemma empiricalPlannerInstance_bounded (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (i : Fin n) :
    ∀ᵐ x ∂(empiricalPlannerInstance y hy).law i, x ≤ 1 := by
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro j _
  simpa using hcap i j

noncomputable def plannerPositiveProbability (y : (i : Fin n) → Fin (k i) → ℝ) (i : Fin n) : ℝ :=
  empiricalPositiveProbability (y i)

noncomputable def plannerActive (y : (i : Fin n) → Fin (k i) → ℝ)
    (A : Finset (Fin n)) : Finset (Fin n) := A.filter (fun i => 0 < plannerPositiveProbability y i)

omit [∀ i, NeZero (k i)] in
lemma plannerPositiveProbability_nonnegative (y : (i : Fin n) → Fin (k i) → ℝ) (i : Fin n) :
    0 ≤ plannerPositiveProbability y i := (empiricalPositiveProbability_mem_unit (y i)).1

omit [∀ i, NeZero (k i)] in
lemma plannerActive_subset (y : (i : Fin n) → Fin (k i) → ℝ) (A : Finset (Fin n)) :
    plannerActive y A ⊆ A := Finset.filter_subset _ _

omit [∀ i, NeZero (k i)] in
lemma plannerActive_positive (y : (i : Fin n) → Fin (k i) → ℝ) (A : Finset (Fin n))
    {i : Fin n} (hi : i ∈ plannerActive y A) : 0 < plannerPositiveProbability y i :=
  (Finset.mem_filter.mp hi).2

omit [∀ i, NeZero (k i)] in
lemma plannerActive_of_positive (y : (i : Fin n) → Fin (k i) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, 0 < plannerPositiveProbability y i) : plannerActive y A = A := by
  ext i
  simp only [plannerActive, Finset.mem_filter, and_iff_left_iff_imp]
  exact hA i

lemma empiricalLaw_constant_zero {r : ℕ} [NeZero r] :
    empiricalLaw (fun _ : Fin r => (0 : ℝ)) = Measure.dirac 0 := by
  ext S hS
  simp only [empiricalLaw, Measure.smul_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (r : ℝ≥0∞)⁻¹ * ((r : ℝ≥0∞) * (Measure.dirac (0 : ℝ)) S) = _
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne r) (by simp), one_mul]

lemma empiricalPlannerInstance_zero_of_not_active
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (i : Fin n) (hi : ¬0 < plannerPositiveProbability y i) :
    (empiricalPlannerInstance y hy).law i = Measure.dirac 0 := by
  have hp : plannerPositiveProbability y i = 0 :=
    le_antisymm (le_of_not_gt hi) (plannerPositiveProbability_nonnegative y i)
  have hcard : (positiveObservations (y i)).card = 0 := by
    unfold plannerPositiveProbability empiricalPositiveProbability at hp
    have hki : (k i : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (k i)
    have hc := (div_eq_zero_iff.mp hp).resolve_right hki
    exact_mod_cast hc
  have hyzero : y i = fun _ => 0 := by
    funext j
    apply le_antisymm _ (hy i j)
    by_contra hn
    have hj : j ∈ positiveObservations (y i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hn⟩
    rw [Finset.card_eq_zero.mp hcard] at hj
    exact Finset.notMem_empty _ hj
  change empiricalLaw (y i) = _
  rw [hyzero]
  exact empiricalLaw_constant_zero

/-- Erasing empirical zeros changes the state representation, not its optimal value. -/
theorem empiricalPlannerInstance_active_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (A : Finset (Fin n)) {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) :
    (empiricalPlannerInstance y hy).continuationValue A u 1 z =
      (empiricalPlannerInstance y hy).continuationValue (plannerActive y A) u 1 z := by
  let D := Finset.univ.filter (fun i : Fin n => 0 < plannerPositiveProbability y i)
  have hzD (i : Fin n) (hi : i ∉ D) : (empiricalPlannerInstance y hy).law i = Measure.dirac 0 := by
    apply empiricalPlannerInstance_zero_of_not_active y hy i
    simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have he : A ∩ D = plannerActive y A := by ext i; simp [D, plannerActive]
  unfold Instance.continuationValue
  have hv := (empiricalPlannerInstance y hy).optimalScalarValue_restrictTo_inter_of_zero A D
    (empiricalPlannerInstance_integrable y hy) hzD zero_le_one (mul_nonneg hz hu)
  exact hv.trans (congrArg (fun S : Finset (Fin n) =>
    optimalScalarValue ((empiricalPlannerInstance y hy).restrictTo S) 1 (z*u)) he)

end ProphetSecretary.Statistics
