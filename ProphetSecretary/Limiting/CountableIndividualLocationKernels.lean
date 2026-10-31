import ProphetSecretary.Limiting.CountableIndividualStationarity
import ProphetSecretary.Limiting.CountableConditionalSelection

/-!
# Conditional kernels in the individual location identity

Independent fresh replacement identifies the selection kernel. The actual
joint law of the individual and its competing maximum identifies the strict
prophet kernel, including marginal atoms at the endpoints.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed : Type*} [MeasurableSpace Seed]

lemma CountableRule.conditionalSelectionAtValue_mem_unit (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) (x : ℝ) :
    π.conditionalSelectionAtValue B ν i x∈Icc (0 : ℝ) 1 := by
  have hm := (π.measurable_individualSelectionIndicator hπ i).comp
    ((measurable_replaceIndividualValue i).comp (measurable_id.prodMk (measurable_const (a := x))))
  have hInt : Integrable (fun v : CompleteWorld Seed => π.individualSelectionIndicator i (replaceIndividualValue i (v,x)))
      (B.completeWorldLaw ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall (fun v => by
      change ‖π.individualSelectionIndicator i (replaceIndividualValue i (v,x))‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg (π.individualSelectionIndicator_mem_unit i _).1]
      exact (π.individualSelectionIndicator_mem_unit i _).2)
  refine ⟨integral_nonneg (fun v => (π.individualSelectionIndicator_mem_unit i _).1),?_⟩
  have h := integral_mono hInt (integrable_const (1 : ℝ)) (fun v => (π.individualSelectionIndicator_mem_unit i (replaceIndividualValue i (v,x))).2)
  simpa only [CountableRule.conditionalSelectionAtValue,integral_const,probReal_univ,one_smul] using h

theorem CountableRule.integral_selection_value_weight (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {D : ℝ} (_hD : 0≤D) (hBound : ∀ x, |φ x|≤D) :
    (∫ v : CompleteWorld Seed, π.individualSelectionIndicator i v*φ (v.2.1 i) ∂B.completeWorldLaw ν)=
      ∫ x, π.conditionalSelectionAtValue B ν i x*φ x ∂(B.individuals i : Measure ℝ) := by
  let F : CompleteWorld Seed → ℝ := fun v => π.individualSelectionIndicator i v*φ (v.2.1 i)
  have hFm : Measurable F := (π.measurable_individualSelectionIndicator hπ i).mul (measurable_individualScore i hφ)
  have hFI : Integrable F (B.completeWorldLaw ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable D
    exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (π.individualSelectionIndicator_mem_unit i v).1]
      exact (mul_le_mul (π.individualSelectionIndicator_mem_unit i v).2 (hBound _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hRep := replaceIndividualValue_measurePreserving B ν i
  have hChange := hRep.hasLaw.integral_comp hFm.aestronglyMeasurable
  calc
    _ = ∫ z, F (replaceIndividualValue i z) ∂(B.completeWorldLaw ν).prod (B.individuals i : Measure ℝ) := hChange.symm
    _ = ∫ x, (∫ v, F (replaceIndividualValue i (v,x)) ∂B.completeWorldLaw ν) ∂(B.individuals i : Measure ℝ) :=
      integral_prod_symm _ (hRep.integrable_comp_of_integrable hFI)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change (∫ v, π.individualSelectionIndicator i (replaceIndividualValue i (v,x))*φ (Function.update v.2.1 i x i)
          ∂B.completeWorldLaw ν)=_
        simp only [Function.update_self]
        rw [integral_mul_const]
        rfl)

lemma integral_individual_strictMaximum_weight (B : CountableInstance) (i : ℕ)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {D : ℝ} (hD : 0≤D) (hBound : ∀ x, |φ x|≤D) :
    (∫ v : CompleteWorld Unit, if B.competingMaximum i v<v.2.1 i then φ (v.2.1 i) else 0 ∂B.completeWorldLaw (Measure.dirac ()))=
      ∫ x, (B.competingMaximumLaw i : Measure ℝ).real (Iio x)*φ x ∂(B.individuals i : Measure ℝ) := by
  let f := fun z : ℝ × ℝ => if z.2<z.1 then φ z.1 else 0
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_snd measurable_fst) (hφ.comp measurable_fst) measurable_const
  have hi : Integrable f ((B.individuals i : Measure ℝ).prod (B.competingMaximumLaw i : Measure ℝ)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable D
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]
      dsimp only [f]
      split_ifs
      · exact hBound _
      · simpa only [abs_zero] using hD)
  have h := (B.individual_competingMaximum_jointLaw i (Measure.dirac ())).integral_comp hm.aestronglyMeasurable
  calc
    _ = ∫ z, f z ∂(B.individuals i : Measure ℝ).prod (B.competingMaximumLaw i : Measure ℝ) := h
    _ = ∫ x, (∫ y, f (x,y) ∂(B.competingMaximumLaw i : Measure ℝ)) ∂(B.individuals i : Measure ℝ) := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simpa only [f,Set.indicator_apply,Set.mem_Iio,smul_eq_mul] using
          integral_indicator_const (μ := (B.competingMaximumLaw i : Measure ℝ)) (φ x) measurableSet_Iio)

end ProphetSecretary.Limiting.CountableInstance
