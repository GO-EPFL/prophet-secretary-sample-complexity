import ProphetSecretary.Limiting.ReserveCutoffWeak
import ProphetSecretary.Limiting.ContinuousWeightedResidual

/-!
# Actual residual offer bands under continuous weighting

Above the reserve, unweighting each weighted marginal recovers its original
law, and unweighting every finite residual recovers its actual aggregate band
measure. This verifies correspondence with the original finite instances.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

noncomputable def reserveBandUnweightHom (w : ℝ →ᵇ ℝ) (a b : ℝ)
    (hw : Monotone w) (hb : a < b) (hwb : 0 < w b) : FiniteMeasure ℝ →+ FiniteMeasure ℝ where
  toFun η := reserveMarkIntensityAbove η w a b hw hb hwb
  map_zero' := by
    apply FiniteMeasure.toMeasure_injective
    change (((0 : Measure ℝ).withDensity (reserveReciprocalWeight w a)).restrict (Ioi b)) = 0
    simp
  map_add' η ξ := by
    apply FiniteMeasure.toMeasure_injective
    change (((η : Measure ℝ)+(ξ : Measure ℝ)).withDensity (reserveReciprocalWeight w a)).restrict (Ioi b) =
      ((η : Measure ℝ).withDensity (reserveReciprocalWeight w a)).restrict (Ioi b) +
      ((ξ : Measure ℝ).withDensity (reserveReciprocalWeight w a)).restrict (Ioi b)
    rw [withDensity_add_measure,Measure.restrict_add]

lemma reserveBand_continuousWeightedLaw (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (a : ℝ) (hw : Monotone w) {b : ℝ} (hb : a < b) (hwb : 0 < w b) :
    reserveMarkIntensityAbove (continuousWeightedLaw p w) w a b hw hb hwb = p.toFiniteMeasure.restrict (Ioi b) := by
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  rw [reserveMarkIntensityAbove_integral,continuousWeightedLaw_integral _ w hw0]
  have heq : (fun x => w x * reserveCutoffTest w b f x) = (Ioi b).indicator f := by
    funext x
    by_cases hx : b < x
    · simp only [reserveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_pos hx,max_eq_right (hw hx.le)]
      have hwx : w x ≠ 0 := ne_of_gt (hwb.trans_le (hw hx.le))
      field_simp
    · simp only [reserveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_neg hx,mul_zero]
  rw [heq,integral_indicator measurableSet_Ioi]
  rfl

theorem reserveBand_weightOrderedResidual {n : ℕ} (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (a : ℝ) (hw : Monotone w) (N : ℕ) {b : ℝ}
    (hb : a < b) (hwb : 0 < w b) :
    reserveMarkIntensityAbove (weightOrderedResidual P w N) w a b hw hb hwb =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
        (weightOrderedMarginalLaw P w i).toFiniteMeasure.restrict (Ioi b) := by
  change reserveBandUnweightHom w a b hw hb hwb (∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
    continuousWeightedLaw (weightOrderedMarginalLaw P w i) w) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact reserveBand_continuousWeightedLaw _ w hw0 a hw hb hwb

end ProphetSecretary.Limiting
