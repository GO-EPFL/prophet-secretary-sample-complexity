import ProphetSecretary.Statistics.PosteriorTargetScoreBound
import ProphetSecretary.Model.ScalarGapMinimum

/-!
# Bounds on the actual posterior gap and empirical error

The weight is an observable unit-range posterior. Its expected true gap
is in [0,1] and dominates the prior average of the actual minimum gap.
First-moment class bounds control the empirical error with no dependence
on the number of variables or prior atoms.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

lemma expectedPosteriorGap_mem_unit (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) :
    F.expectedPosteriorGap N b k∈Icc (0 : ℝ) 1 := by
  have hSum : (∑ θ : Fin F.size, (F.weight θ : ℝ))=1 := by exact_mod_cast F.weight_sum
  have hEach (θ : Fin F.size) :
      (∫ p : Reservoir n (trainingLength N b k) × Unit,
        normalizedScalarGap (F.offerInstance θ)
          (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
        ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod (Measure.dirac ()))∈Icc (0 : ℝ) 1 := by
    let D := ((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod (Measure.dirac ())
    let W := fun p : Reservoir n (trainingLength N b k) × Unit =>
      F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)
    have hm : Measurable W := (F.measurable_boundedPosteriorFromObservation N b k).comp
      ((measurable_extendTrainingPrefix n N b k).comp measurable_fst)
    have hr (p) : W p∈Icc (0 : ℝ) 1 := F.boundedPosteriorFromObservation_mem_unit N b k _
    have hInt := (F.offerInstance θ).integrable_normalizedGap_of_weight (hcap θ) D hm hr
    refine ⟨integral_nonneg (fun p => ((F.offerInstance θ).normalizedScalarGap_mem_unit (hcap θ) (hr p)).1),?_⟩
    have hUpper := integral_mono hInt (integrable_const (1 : ℝ))
      (fun p => ((F.offerInstance θ).normalizedScalarGap_mem_unit (hcap θ) (hr p)).2)
    simpa only [integral_const,probReal_univ,one_smul] using hUpper
  refine ⟨Finset.sum_nonneg (fun θ _ => mul_nonneg (F.weight θ).coe_nonneg (hEach θ).1),?_⟩
  calc
    _ ≤ ∑ θ : Fin F.size, (F.weight θ : ℝ)*1 :=
      Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left (hEach θ).2 (F.weight θ).coe_nonneg)
    _ = 1 := by simpa only [mul_one] using hSum

lemma expectedPosteriorGap_ge_mean_minimum (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) :
    (∑ θ : Fin F.size, (F.weight θ : ℝ)*minimumNormalizedScalarGap (F.offerInstance θ))≤
      F.expectedPosteriorGap N b k := by
  apply Finset.sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left _ (F.weight θ).coe_nonneg
  let P := F.offerInstance θ
  let D := (P.reservoirLaw (trainingLength N b k)).prod (Measure.dirac ())
  let W := fun p : Reservoir n (trainingLength N b k) × Unit =>
    F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)
  have hm : Measurable W := (F.measurable_boundedPosteriorFromObservation N b k).comp
    ((measurable_extendTrainingPrefix n N b k).comp measurable_fst)
  have hr (p) : W p∈Icc (0 : ℝ) 1 := F.boundedPosteriorFromObservation_mem_unit N b k _
  have hInt := P.integrable_normalizedGap_of_weight (hcap θ) D hm hr
  have hLower := integral_mono (integrable_const (minimumNormalizedScalarGap P)) hInt
    (fun p => intervalNormalizedScalarGapMinimum_le P (P.integrable_maximum_of_bounded (hcap θ)) le_rfl le_rfl (hr p))
  simpa only [integral_const,probReal_univ,one_smul] using hLower

omit [NeZero m] in
lemma posteriorEmpiricalError_le_of_firstMoment_bound (F : FinitePrior n) {lo S0 : ℝ}
    (hlo : 0<lo) (hlohi : lo≤1/4)
    (hS : ∀ θ, (F.offerInstance θ).totalFirstMoment≤S0) :
    F.posteriorEmpiricalError lo m≤empiricalCapRegretConstant lo*(1+S0*(1+S0))/(m : ℝ) := by
  have hSum : (∑ θ : Fin F.size, (F.weight θ : ℝ))=1 := by exact_mod_cast F.weight_sum
  have hK := (empiricalCapRegretConstant_positive hlo hlohi).le
  unfold posteriorEmpiricalError
  calc
    _ ≤ ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        (empiricalCapRegretConstant lo*(1+S0*(1+S0))/(m : ℝ)) := by
      apply Finset.sum_le_sum
      intro θ _
      apply mul_le_mul_of_nonneg_left _ (F.weight θ).coe_nonneg
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
      apply mul_le_mul_of_nonneg_left _ hK
      have hNonneg : 0≤(F.offerInstance θ).totalFirstMoment :=
        Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae ((F.offerInstance θ).nonnegative i))
      have hSq := mul_self_le_mul_self hNonneg (hS θ)
      nlinarith only [hSq,hS θ]
    _ = _ := by rw [←Finset.sum_mul,hSum,one_mul]

end ProphetSecretary.Statistics.FinitePrior
