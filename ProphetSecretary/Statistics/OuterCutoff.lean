import ProphetSecretary.Statistics.OuterCutoffLaw
import ProphetSecretary.Model.OuterRetainedMeanConditioning
import ProphetSecretary.Model.OuterRetainedCountMeasurability

/-!
# Independent cutoff reduction

The cutoff uses m complete training rounds and independent uniform tags. Fresh
retained offers have the stated independent product law conditional on this
cutoff. Their expected maximum loses at most the fraction 1/(m+1), while their
positive tail count exceeds 2 log m with probability at most 1/m.
Paper correspondence: `upouter:cutoff`.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

lemma outerCutoff_retainedMaximum_integrable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 1≤m) :
    Integrable (fun p => (P.retainedAtTag (outerCutoff m hm p)).expectedMaximum) (outerCutoffDataLaw P m) :=
  P.integrable_retainedAtTag_expectedMaximum hP _ (measurable_outerCutoff m hm)

/-- Expected retained prophet value, including the empty instance. -/
theorem outerCutoff_retainedMaximum_mean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 1≤m) :
    ((m:ℝ)/((m:ℝ)+1))*P.expectedMaximum≤
      ∫ p, (P.retainedAtTag (outerCutoff m hm p)).expectedMaximum ∂outerCutoffDataLaw P m := by
  by_cases hn : 0<n
  · have hQm := measurable_outerCutoff_score P hn m hm
    have hQI : Integrable (fun p => P.taggedVoidProbability (outerCutoff m hm p)) (outerCutoffDataLaw P m) := by
      apply Integrable.of_bound hQm.aestronglyMeasurable 1
      exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (P.taggedVoidProbability_mem_unit _).1]
        exact (P.taggedVoidProbability_mem_unit _).2
    have hLI : Integrable (fun p => (1-P.taggedVoidProbability (outerCutoff m hm p))*P.expectedMaximum) (outerCutoffDataLaw P m) :=
      ((integrable_const 1).sub hQI).mul_const _
    have hLE := integral_mono hLI (outerCutoff_retainedMaximum_integrable P hP m hm)
      (fun p => P.retainedAtTag_expectedMaximum_lower hP (outerCutoff m hm p))
    rw [integral_mul_const,integral_sub (integrable_const 1) hQI,
      integral_outerCutoff_score P hn m hm] at hLE
    simp only [integral_const,probReal_univ,one_smul] at hLE
    have hCoeff : (m:ℝ)/((m:ℝ)+1)=1-1/((m:ℝ)+1) := by
      field_simp
      ring
    rwa [hCoeff]
  · have hn0 : n=0 := by omega
    subst n
    have hMaximum : (Instance.maximum : (Fin 0 → ℝ) → ℝ)=fun _ => 0 := by
      funext x
      exact le_antisymm (Instance.maximum_le x le_rfl (fun i => Fin.elim0 i)) (Instance.maximum_nonnegative x)
    have hM : P.expectedMaximum=0 := by simp only [Instance.expectedMaximum,hMaximum,integral_zero]
    rw [hM,mul_zero]
    exact integral_nonneg (fun p => (P.retainedAtTag _).expectedMaximum_nonnegative)

/-- The high-probability positive-count comparison holds even for n=0 and m=1. -/
theorem outerCutoff_positiveCount_probability (P : Instance n) (m : ℕ) (hm : 1≤m) :
    (outerCutoffDataLaw P m).real {p | 2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount}≤1/(m:ℝ) := by
  by_cases hn : 0<n
  · refine (measureReal_mono (μ:=outerCutoffDataLaw P m) ?_ (measure_ne_top _ _)).trans
      (outerCutoff_small_score_probability P hn m hm)
    intro p hp
    change 2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount at hp
    change P.taggedVoidProbability (outerCutoff m hm p)<1/(m:ℝ)^2
    by_contra h
    exact (not_lt_of_ge (P.retainedAtTag_positiveCount_le_two_log _ hm (le_of_not_gt h))) hp
  · have hn0 : n=0 := by omega
    subst n
    have hmR : (1:ℝ)≤m := by exact_mod_cast hm
    have hLog : 0≤Real.log (m:ℝ) := Real.log_nonneg hmR
    have hSet : {p : Reservoir 0 m × (Fin m → Fin 0 → ℝ) |
        2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount}=∅ := by
      ext p
      simp only [Set.mem_setOf_eq,Instance.positiveCount,Instance.tailCount,Finset.univ_eq_empty,Finset.sum_empty,Set.mem_empty_iff_false,iff_false]
      linarith
    rw [hSet,measureReal_empty]
    positivity

lemma measurableSet_outerCutoff_positiveCount_failure (P : Instance n) (m : ℕ) (hm : 1≤m) :
    MeasurableSet {p : Reservoir n m × (Fin m → Fin n → ℝ) |
      2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount} :=
  measurableSet_lt measurable_const (P.measurable_retainedAtTag_positiveCount.comp (measurable_outerCutoff m hm))

/-- Conditional product-law identity for every bounded measurable test function. -/
theorem outerCutoff_conditional_retainedLaw (P : Instance n) (m : ℕ) (hm : 1≤m)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖≤C) :
    ((outerCutoffDataLaw P m).prod P.taggedValuesLaw)[
      (fun p => f (retainedTaggedVector (outerCutoff m hm p.1) p.2))|
      MeasurableSpace.comap (fun p : (Reservoir n m × (Fin m → Fin n → ℝ)) × (Fin n → ℝ × ℝ) => outerCutoff m hm p.1) inferInstance]
      =ᵐ[(outerCutoffDataLaw P m).prod P.taggedValuesLaw]
      (fun p => ∫ y, f y ∂(P.retainedAtTag (outerCutoff m hm p.1)).valuesLaw) :=
  P.retainedTaggedVector_condExp _ (measurable_outerCutoff m hm) hf hC

/-- The same conditional law determines the unbounded integrable maximum. -/
theorem outerCutoff_conditional_retainedMaximum (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 1≤m) :
    ((outerCutoffDataLaw P m).prod P.taggedValuesLaw)[
      (fun p => retainedMaximumAtTag (outerCutoff m hm p.1) p.2)|
      MeasurableSpace.comap (fun p : (Reservoir n m × (Fin m → Fin n → ℝ)) × (Fin n → ℝ × ℝ) => outerCutoff m hm p.1) inferInstance]
      =ᵐ[(outerCutoffDataLaw P m).prod P.taggedValuesLaw]
      (fun p => (P.retainedAtTag (outerCutoff m hm p.1)).expectedMaximum) :=
  P.retainedMaximumAtTag_condExp hP _ (measurable_outerCutoff m hm)

/-- Finite statistical cutoff reduction, with a hard budget on every transcript. -/
theorem outer_cutoff (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) :
    (∀ p : Reservoir n m × (Fin m → Fin n → ℝ),
      (P.retainedAtTag (outerCutoff m hm p)).expectedMaximum≤P.expectedMaximum) ∧
    Integrable (fun p => (P.retainedAtTag (outerCutoff m hm p)).expectedMaximum) (outerCutoffDataLaw P m) ∧
    (((m:ℝ)/((m:ℝ)+1))*P.expectedMaximum≤
      ∫ p, (P.retainedAtTag (outerCutoff m hm p)).expectedMaximum ∂outerCutoffDataLaw P m) ∧
    MeasurableSet {p : Reservoir n m × (Fin m → Fin n → ℝ) |
      2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount} ∧
    ((outerCutoffDataLaw P m).real {p | 2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount}≤1/(m:ℝ)) ∧
    (∀ (tags : Fin m → Fin n → ℝ) (y : Reservoir n m) (i : Fin n), requests (trainingTranscript (requestAll m) tags y) i≤m) := by
  exact ⟨fun p => P.retainedAtTag_expectedMaximum_le hP _,
    outerCutoff_retainedMaximum_integrable P hP m hm,
    outerCutoff_retainedMaximum_mean P hP m hm,
    measurableSet_outerCutoff_positiveCount_failure P m hm,
    outerCutoff_positiveCount_probability P m hm,
    fun tags y i => outerCutoff_hardBudget m tags y i⟩

end ProphetSecretary.Statistics
