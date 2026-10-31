import ProphetSecretary.Limiting.CountableValueReplacement
import ProphetSecretary.Limiting.CountablePolicyBounds

/-!
# Actual duration conditional on one countable individual value

Independent replacement constructs the conditional-duration kernel from a
fixed callback. It is measurable and unit bounded. Its score identity follows
from the actual replacement pushforward and Fubini, with no future offer
information supplied to the policy and no reoptimization after replacement.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def CountableRule.durationAtValue (π : CountableRule Seed) (i : ℕ)
    (z : CompleteWorld Seed × ℝ) : ℝ := π.realizedDuration (replaceIndividualValue i z)

lemma CountableRule.measurable_durationAtValue (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ) :
    Measurable (π.durationAtValue i) := (π.measurable_realizedDuration hπ).comp (measurable_replaceIndividualValue i)

noncomputable def CountableRule.conditionalDurationAtValue (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) (i : ℕ) (x : ℝ) : ℝ :=
  ∫ v, π.durationAtValue i (v,x) ∂B.completeWorldLaw ν

lemma CountableRule.measurable_conditionalDurationAtValue (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    Measurable (π.conditionalDurationAtValue B ν i) :=
  (π.measurable_durationAtValue hπ i).stronglyMeasurable.integral_prod_left'.measurable

lemma CountableRule.integrable_durationAtValue_fixed (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) (x : ℝ) :
    Integrable (fun v : CompleteWorld Seed => π.durationAtValue i (v,x)) (B.completeWorldLaw ν) := by
  have hm := (π.measurable_durationAtValue hπ i).comp
    (measurable_id.prodMk (measurable_const (a := x)))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall (fun v => by
    change ‖π.realizedDuration (replaceIndividualValue i (v,x))‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (π.duration_bounds (replaceIndividualValue i (v,x))).1]
    exact (π.duration_bounds (replaceIndividualValue i (v,x))).2)

lemma CountableRule.conditionalDurationAtValue_mem_unit (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) (x : ℝ) :
    π.conditionalDurationAtValue B ν i x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun v => (π.duration_bounds (replaceIndividualValue i (v,x))).1)
  · have h := integral_mono (π.integrable_durationAtValue_fixed hπ B ν i x) (integrable_const (1 : ℝ))
      (fun v => (π.duration_bounds (replaceIndividualValue i (v,x))).2)
    simpa only [CountableRule.conditionalDurationAtValue,integral_const,probReal_univ,one_smul] using h

omit [MeasurableSpace Seed] in
lemma CountableRule.durationAtValue_self (π : CountableRule Seed) (i : ℕ) (v : CompleteWorld Seed) :
    π.durationAtValue i (v,v.2.1 i)=π.realizedDuration v := by
  unfold CountableRule.durationAtValue
  rw [replaceIndividualValue_self]

/-- Complete-value scores may inspect Xi even when it arrives after stopping;
this integral identity does not make that value an online observation. -/
theorem CountableRule.integral_duration_value_weight (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, |φ x| ≤ 1) :
    (∫ v : CompleteWorld Seed, φ (v.2.1 i)*π.realizedDuration v ∂B.completeWorldLaw ν)=
      ∫ x, φ x*π.conditionalDurationAtValue B ν i x ∂(B.individuals i : Measure ℝ) := by
  let F : CompleteWorld Seed → ℝ := fun v => φ (v.2.1 i)*π.realizedDuration v
  have hFm : Measurable F :=
    (hφ.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).mul (π.measurable_realizedDuration hπ)
  have hFI : Integrable F (B.completeWorldLaw ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (π.duration_bounds v).1]
      exact mul_le_one₀ (hb _) (π.duration_bounds v).1 (π.duration_bounds v).2)
  have hRep := replaceIndividualValue_measurePreserving B ν i
  have hChange := integral_map (μ := (B.completeWorldLaw ν).prod (B.individuals i : Measure ℝ))
    hRep.measurable.aemeasurable hFm.aestronglyMeasurable
  rw [hRep.map_eq] at hChange
  calc
    _ = ∫ z, F (replaceIndividualValue i z) ∂(B.completeWorldLaw ν).prod (B.individuals i : Measure ℝ) := hChange
    _ = ∫ x, (∫ v, F (replaceIndividualValue i (v,x)) ∂B.completeWorldLaw ν) ∂(B.individuals i : Measure ℝ) :=
      integral_prod_symm _ (hRep.integrable_comp_of_integrable hFI)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change (∫ v : CompleteWorld Seed, φ (Function.update v.2.1 i x i)*π.durationAtValue i (v,x)
          ∂B.completeWorldLaw ν)=_
        simp only [Function.update_self]
        rw [integral_const_mul]
        rfl)

end ProphetSecretary.Limiting.CountableInstance
