import ProphetSecretary.Model.EmpiricalConditionalValues
import ProphetSecretary.Model.LearnerConditioning
import ProphetSecretary.Model.SharpNormalizedRegret
import ProphetSecretary.Model.UnitScalarGap

/-!
# Integrability of selected gaps and frozen scores

Weights are measurable functions of training data and lie in the unit
interval on every raw input. The scalar value and frozen policy are kept
distinct. These bounds justify integration of the pointwise clamp.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Model
variable {n k : ℕ}

lemma Instance.integrable_normalizedGap_of_weight {Ω : Type*} [MeasurableSpace Ω]
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1)
    (D : Measure Ω) [IsFiniteMeasure D] {W : Ω → ℝ}
    (hW : Measurable W) (hRange : ∀ d, W d∈Icc (0 : ℝ) 1) :
    Integrable (fun d => normalizedScalarGap P (W d)) D := by
  apply Integrable.of_bound (P.measurable_normalizedGap_of_weight
    (P.integrable_maximum_of_bounded hcap) hW hRange).aestronglyMeasurable 1
  exact Eventually.of_forall (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (P.normalizedScalarGap_mem_unit hcap (hRange d)).1]
    exact (P.normalizedScalarGap_mem_unit hcap (hRange d)).2)

lemma Learner.integrable_frozenNormalizedRegret (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D]
    {W : Reservoir n k × L.Seed → ℝ} (hW : Measurable W) (hRange : ∀ d, W d∈Icc (0 : ℝ) 1) :
    Integrable (fun d => (L.frozenRandomizedPolicy d.1 d.2).normalizedRegret P (W d)) D := by
  have hV := P.measurable_scalarValue_coefficients hP hW (measurable_const.sub hW)
    (fun d => (hRange d).1) (fun d => sub_nonneg.mpr (hRange d).2)
  have hJ : Measurable (fun d : Reservoir n k × L.Seed =>
      (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P (W d) (1-W d)) :=
    L.measurable_frozenScalarObjective P hP hW (measurable_const.sub hW)
  apply Integrable.of_bound (hV.sub hJ).aestronglyMeasurable (P.expectedMaximum+1)
  filter_upwards [] with d
  let π := L.frozenRandomizedPolicy d.1 d.2
  have hR0 := π.normalizedRegret_nonnegative P hP (hRange d)
  have hVal := optimalScalarValue_le_benchmark P hP (hRange d).1 (sub_nonneg.mpr (hRange d).2)
  have hJ0 := π.scalarObjective_nonnegative P hP (hRange d).1 (sub_nonneg.mpr (hRange d).2)
  have hM := mul_le_of_le_one_left P.expectedMaximum_nonnegative (hRange d).2
  change |π.normalizedRegret P (W d)|≤P.expectedMaximum+1
  rw [abs_of_nonneg hR0]
  unfold RandomizedPolicy.normalizedRegret
  linarith only [hVal,hJ0,hM,(hRange d).1]

lemma Learner.integrable_frozenSelectedObjective (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D]
    {W : Reservoir n k × L.Seed → ℝ} (hW : Measurable W) (hRange : ∀ d, W d∈Icc (0 : ℝ) 1) :
    Integrable (fun d => (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P (W d) (1-W d)) D := by
  have hBound : ∀ᵐ d ∂D, ‖W d‖≤1 := Eventually.of_forall (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hRange d).1];exact (hRange d).2)
  have hComp : ∀ᵐ d ∂D, ‖1-W d‖≤1 := Eventually.of_forall (fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hRange d).2)]
    linarith only [(hRange d).1])
  have hR := (L.integrable_frozenExpectedReward P hP D).bdd_mul hW.aestronglyMeasurable hBound
  have hT := (L.integrable_frozenExpectedDuration P D).bdd_mul
    (measurable_const.sub hW).aestronglyMeasurable hComp
  apply (hR.add hT).congr
  exact Eventually.of_forall (fun d =>
    ((L.frozenRandomizedPolicy d.1 d.2).scalarObjective_eq P hP (W d) (1-W d)).symm)

lemma Learner.integrable_frozenSelectedScore (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D]
    {W : Reservoir n k × L.Seed → ℝ} (hW : Measurable W) (hRange : ∀ d, W d∈Icc (0 : ℝ) 1) (C : ℝ) :
    Integrable (fun d => (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P (W d) (1-W d)-
      C*(W d*P.expectedMaximum+1-W d)) D := by
  have hWI : Integrable W D := Integrable.of_bound hW.aestronglyMeasurable 1
    (Eventually.of_forall (fun d => by rw [Real.norm_eq_abs,abs_of_nonneg (hRange d).1];exact (hRange d).2))
  exact (L.integrable_frozenSelectedObjective P hP D hW hRange).sub
    ((((hWI.mul_const P.expectedMaximum).add (integrable_const 1)).sub hWI).const_mul C)

end ProphetSecretary.Model
