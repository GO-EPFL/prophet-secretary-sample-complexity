import ProphetSecretary.Model.Instance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-!
# Finite-support maxima from marginal distribution functions

The atom of a positive maximum is the difference between the products of
the closed and strict marginal distribution functions. A zero atom has no
contribution to the mean. These identities include the empty instance.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n : ℕ}

lemma maximum_closedCDF (P : Instance n) {a : ℝ} (ha : 0 ≤ a) :
    P.valuesLaw.real {x | Instance.maximum x ≤ a} = ∏ i, (P.law i).real (Iic a) := by
  have hSet : {x : Fin n → ℝ | Instance.maximum x ≤ a} = Set.univ.pi (fun _ : Fin n => Iic a) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Iic]
    constructor
    · intro h i
      exact (Instance.le_maximum x i).trans h
    · exact Instance.maximum_le x ha
  change (P.valuesLaw {x | Instance.maximum x ≤ a}).toReal = _
  rw [hSet, Instance.valuesLaw, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

lemma maximum_strictCDF (P : Instance n) {a : ℝ} (ha : 0 < a) :
    P.valuesLaw.real {x | Instance.maximum x < a} = ∏ i, (P.law i).real (Iio a) := by
  have hSet : {x : Fin n → ℝ | Instance.maximum x < a} = Set.univ.pi (fun _ : Fin n => Iio a) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Iio]
    constructor
    · intro h i
      exact (Instance.le_maximum x i).trans_lt h
    · intro h
      unfold Instance.maximum
      apply (Finset.sup'_lt_iff _).mpr
      intro i _
      cases i with
      | none => exact ha
      | some i => exact h i
  change (P.valuesLaw {x | Instance.maximum x < a}).toReal = _
  rw [hSet, Instance.valuesLaw, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

lemma maximum_positive_atom (P : Instance n) {a : ℝ} (ha : 0 < a) :
    P.valuesLaw.real {x | Instance.maximum x = a} =
      (∏ i, (P.law i).real (Iic a)) - ∏ i, (P.law i).real (Iio a) := by
  have hMeas : MeasurableSet {x : Fin n → ℝ | Instance.maximum x = a} :=
    Instance.measurable_maximum (measurableSet_singleton a)
  have hDis : Disjoint {x : Fin n → ℝ | Instance.maximum x < a}
      {x | Instance.maximum x = a} := by
    apply Set.disjoint_left.mpr
    intro x hx he
    change Instance.maximum x < a at hx
    change Instance.maximum x = a at he
    rw [he] at hx
    exact lt_irrefl a hx
  have hUnion : {x : Fin n → ℝ | Instance.maximum x < a} ∪ {x | Instance.maximum x = a} =
      {x | Instance.maximum x ≤ a} := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, le_iff_lt_or_eq]
  have h := measureReal_union (μ := P.valuesLaw) hDis hMeas
  rw [hUnion, maximum_closedCDF P ha.le, maximum_strictCDF P ha] at h
  linarith

lemma maximum_mem_support (P : Instance n) (G : Finset ℝ) (hZero : 0 ∈ G)
    (hSupport : ∀ i, ∀ᵐ v ∂P.law i, v ∈ G) :
    ∀ᵐ x ∂P.valuesLaw, Instance.maximum x ∈ G := by
  have hValues : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ∈ G :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hSupport i))
  filter_upwards [hValues] with x hx
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset (Option (Fin n))).Nonempty from ⟨none, Finset.mem_univ _⟩)
    (fun i : Option (Fin n) => i.elim 0 x)
  change Instance.maximum x = i.elim 0 x at hi
  rw [hi]
  cases i with
  | none => exact hZero
  | some i => exact hx i

lemma expectedMaximum_eq_atom_sum (P : Instance n) (G : Finset ℝ) (hZero : 0 ∈ G)
    (hSupport : ∀ i, ∀ᵐ v ∂P.law i, v ∈ G) :
    P.expectedMaximum = ∑ a ∈ G, a * P.valuesLaw.real {x | Instance.maximum x = a} := by
  let f : ℝ → (Fin n → ℝ) → ℝ := fun a => {x | Instance.maximum x = a}.indicator (fun _ => a)
  have hMeas (a : ℝ) : MeasurableSet {x : Fin n → ℝ | Instance.maximum x = a} :=
    Instance.measurable_maximum (measurableSet_singleton a)
  have hEach (a : ℝ) : Integrable (f a) P.valuesLaw := (integrable_const a).indicator (hMeas a)
  have hPoint : Instance.maximum =ᵐ[P.valuesLaw] fun x => ∑ a ∈ G, f a x := by
    filter_upwards [maximum_mem_support P G hZero hSupport] with x hx
    simp [f, Set.indicator_apply, hx, eq_comm]
  rw [Instance.expectedMaximum, integral_congr_ae hPoint, integral_finsetSum G (fun a _ => hEach a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator_const a (hMeas a)]
  simp only [smul_eq_mul, mul_comm]

/-- Exact finite-support computation, with no enumeration of offer profiles. -/
theorem expectedMaximum_eq_CDF_atom_sum (P : Instance n) (G : Finset ℝ) (hZero : 0 ∈ G)
    (hNonneg : ∀ a ∈ G, 0 ≤ a) (hSupport : ∀ i, ∀ᵐ v ∂P.law i, v ∈ G) :
    P.expectedMaximum = ∑ a ∈ G, a *
      ((∏ i, (P.law i).real (Iic a)) - ∏ i, (P.law i).real (Iio a)) := by
  rw [expectedMaximum_eq_atom_sum P G hZero hSupport]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : a = 0
  · subst a
    simp
  · rw [maximum_positive_atom P (lt_of_le_of_ne (hNonneg a ha) (fun h => hz h.symm))]

end ProphetSecretary.Statistics
