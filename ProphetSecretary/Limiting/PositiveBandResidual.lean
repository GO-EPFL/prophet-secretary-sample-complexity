import ProphetSecretary.Limiting.PositiveCutoffWeak
import ProphetSecretary.Limiting.OrderedWeightedResidual

/-!
# Actual residual offer bands from their weighted measures

Unweighting and restricting to a positive band commutes with positive finite
sums. For a marginal supported in the cap interval it exactly recovers that
marginal restricted to the band. Thus the weak weighted residuals correspond
to the paper's actual residual aggregate measures, not replacement data.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

lemma positiveMarkIntensityAbove_zero {b : ℝ} (hb : 0 < b) : positiveMarkIntensityAbove 0 b hb = 0 := by
  apply FiniteMeasure.toMeasure_injective
  change (((0 : Measure ℝ).withDensity positiveReciprocalWeight).restrict (Ioi b)) = 0
  simp

lemma positiveMarkIntensityAbove_add (η ξ : FiniteMeasure ℝ) {b : ℝ} (hb : 0 < b) :
    positiveMarkIntensityAbove (η+ξ) b hb = positiveMarkIntensityAbove η b hb + positiveMarkIntensityAbove ξ b hb := by
  apply FiniteMeasure.toMeasure_injective
  change (((η : Measure ℝ)+(ξ : Measure ℝ)).withDensity positiveReciprocalWeight).restrict (Ioi b) =
    ((η : Measure ℝ).withDensity positiveReciprocalWeight).restrict (Ioi b) +
    ((ξ : Measure ℝ).withDensity positiveReciprocalWeight).restrict (Ioi b)
  rw [withDensity_add_measure,Measure.restrict_add]

noncomputable def positiveBandUnweightHom (b : ℝ) (hb : 0 < b) : FiniteMeasure ℝ →+ FiniteMeasure ℝ where
  toFun η := positiveMarkIntensityAbove η b hb
  map_zero' := positiveMarkIntensityAbove_zero hb
  map_add' η ξ := positiveMarkIntensityAbove_add η ξ hb

/-- Unweighting above b recovers the actual marginal law above b. -/
lemma positiveBand_valueWeightedLaw (p : ProbabilityMeasure ℝ) (H : ℝ≥0)
    (hcap : ∀ᵐ x ∂(p : Measure ℝ), x ∈ Icc (0 : ℝ) H) {b : ℝ} (hb : 0 < b) :
    positiveMarkIntensityAbove (valueWeightedLaw p H) b hb = p.toFiniteMeasure.restrict (Ioi b) := by
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  rw [positiveMarkIntensityAbove_integral,valueWeightedLaw_integral]
  have heq : (fun x => boundedOfferValue H x * positiveCutoffTest b f x) =ᵐ[(p : Measure ℝ)] (Ioi b).indicator f := by
    filter_upwards [hcap] with x hx
    rw [boundedOfferValue_eq H hx]
    by_cases hxb : b < x
    · simp only [positiveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_pos hxb,max_eq_right hxb.le]
      have hx0 : x ≠ 0 := ne_of_gt (hb.trans hxb)
      field_simp
    · simp only [positiveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_neg hxb,mul_zero]
  rw [integral_congr_ae heq,integral_indicator measurableSet_Ioi]
  rfl

/-- Actual residual band measure after an arbitrary finite retained prefix. -/
theorem positiveBand_orderedWeightedResidual {n : ℕ} (P : Model.Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) (N : ℕ) {b : ℝ} (hb : 0 < b) :
    positiveMarkIntensityAbove (orderedWeightedResidual P H N) b hb =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
        (orderedMarginalLaw P i).toFiniteMeasure.restrict (Ioi b) := by
  change positiveBandUnweightHom b hb (∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
    valueWeightedLaw (orderedMarginalLaw P i) H) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact positiveBand_valueWeightedLaw _ H (ae_iff.mpr (orderedMarginalLaw_supported_interval P H.coe_nonneg hcap i)) hb

end ProphetSecretary.Limiting
