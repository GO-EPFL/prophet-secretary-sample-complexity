import ProphetSecretary.Probability.CompensatedCloudTilt
import ProphetSecretary.Limiting.LabeledBandConvergence

/-!
# Actual residual complement-compensated finite laws

Only labels at or beyond the retained prefix are tilted. The score is one
on the band and minus p/(1-p) on its full complement, including zero and low
positive values. A row with any residual band mass above one half is left
unchanged. Such exceptional rows eventually disappear on the residual diagonal.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

def ResidualBandSmall (P : Model.Instance n) (N : ℕ) (S : Set ℝ) : Prop :=
  ∀ j : Fin n, N≤j.val → (P.law j).real S≤1/2

noncomputable def residualCompensatedScore (P : Model.Instance n) (N : ℕ) (S : Set ℝ) : Fin n → ℝ → ℝ :=
  fun j x => if N≤j.val then compensatedBandScore (P.law j) S x else 0

lemma residualCompensatedScore_properties (P : Model.Instance n) (N : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (hSmall : ResidualBandSmall P N S) :
    (∀ j, Measurable (residualCompensatedScore P N S j)) ∧
      (∀ j x, |residualCompensatedScore P N S j x|≤1) ∧
      (∀ j, (∫ x, residualCompensatedScore P N S j x ∂P.law j)=0) := by
  constructor
  · intro j
    change Measurable (fun x : ℝ => if N≤j.val then compensatedBandScore (P.law j) S x else 0)
    by_cases hj : N≤j.val
    · simpa only [if_pos hj] using measurable_compensatedBandScore (P.law j) hS
    · simp only [if_neg hj]
      exact measurable_const
  constructor
  · intro j x
    by_cases hj : N≤j.val
    · simpa only [residualCompensatedScore,if_pos hj] using compensatedBandScore_abs_le_one (P.law j) (hSmall j hj) x
    · simp only [residualCompensatedScore,if_neg hj,abs_zero,zero_le_one]
  · intro j
    by_cases hj : N≤j.val
    · simpa only [residualCompensatedScore,if_pos hj] using compensatedBandScore_mean (P.law j) hS
        (show (P.law j).real S<1 by linarith only [hSmall j hj])
    · simp only [residualCompensatedScore,if_neg hj,integral_zero]

noncomputable def compensatedResidualOffers (P : Model.Instance n) (N : ℕ) (S : Set ℝ)
    (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) : Model.Instance n :=
  if hSmall : ResidualBandSmall P N S then
    P.likelihoodTilt (residualCompensatedScore P N S)
      (residualCompensatedScore_properties P N hS hSmall).1
      (fun j => Filter.Eventually.of_forall ((residualCompensatedScore_properties P N hS hSmall).2.1 j))
      (residualCompensatedScore_properties P N hS hSmall).2.2 θ hθ
  else P

lemma compensatedResidualOffers_bounded (P : Model.Instance n) (N : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (θ : ℝ) (hθ : |θ|≤1/4) {H : ℝ} (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤H) :
    ∀ j, ∀ᵐ x ∂(compensatedResidualOffers P N S hS θ hθ).law j, x≤H := by
  unfold compensatedResidualOffers
  split_ifs with hSmall
  · intro j
    exact (tiltLaw_absolutelyContinuous (P.law j) (residualCompensatedScore P N S j) θ).ae_le (hCap j)
  · exact hCap

lemma compensatedResidualOffers_law_before (P : Model.Instance n) (N : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (θ : ℝ) (hθ : |θ|≤1/4) (j : Fin n) (hj : j.val<N) :
    (compensatedResidualOffers P N S hS θ hθ).law j=P.law j := by
  unfold compensatedResidualOffers
  split_ifs with hSmall
  · have hScore : residualCompensatedScore P N S j=(fun _ => 0) := by
      funext x
      simp only [residualCompensatedScore,if_neg (not_le.mpr hj)]
    change tiltLaw (P.law j) (residualCompensatedScore P N S j) θ=P.law j
    rw [hScore]
    simp only [tiltLaw,tiltFactor,mul_zero,add_zero,ENNReal.ofReal_one]
    exact withDensity_one
  · rfl

lemma compensatedResidualOffers_law_residual (P : Model.Instance n) (N : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (θ : ℝ) (hθ : |θ|≤1/4) (hSmall : ResidualBandSmall P N S) (j : Fin n) (hj : N≤j.val) :
    (compensatedResidualOffers P N S hS θ hθ).law j=tiltLaw (P.law j) (compensatedBandScore (P.law j) S) θ := by
  rw [compensatedResidualOffers,dif_pos hSmall]
  change tiltLaw (P.law j) (residualCompensatedScore P N S j) θ=_
  have hScore : residualCompensatedScore P N S j=compensatedBandScore (P.law j) S := by
    funext x
    simp only [residualCompensatedScore,if_pos hj]
  rw [hScore]

lemma tiltLaw_quarter_measure_bounds (μ : Measure ℝ) (score : ℝ → ℝ)
    (hBound : ∀ᵐ x ∂μ, |score x|≤1) (θ : ℝ) (hθ : |θ|≤1/4) :
    ENNReal.ofReal (3/4) • μ≤tiltLaw μ score θ ∧ tiltLaw μ score θ≤ENNReal.ofReal (5/4) • μ := by
  constructor
  · rw [tiltLaw,←withDensity_const]
    exact withDensity_mono (hBound.mono (fun x hx => ENNReal.ofReal_le_ofReal (tiltFactor_bounds hθ hx).1))
  · rw [tiltLaw,←withDensity_const]
    exact withDensity_mono (hBound.mono (fun x hx => ENNReal.ofReal_le_ofReal (tiltFactor_bounds hθ hx).2))

lemma compensatedResidualOffers_measure_bounds (P : Model.Instance n) (N : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (θ : ℝ) (hθ : |θ|≤1/4) (j : Fin n) :
    ENNReal.ofReal (3/4) • P.law j≤(compensatedResidualOffers P N S hS θ hθ).law j ∧
      (compensatedResidualOffers P N S hS θ hθ).law j≤ENNReal.ofReal (5/4) • P.law j := by
  unfold compensatedResidualOffers
  split_ifs with hSmall
  · exact tiltLaw_quarter_measure_bounds (P.law j) (residualCompensatedScore P N S j)
      (Filter.Eventually.of_forall ((residualCompensatedScore_properties P N hS hSmall).2.1 j)) θ hθ
  · constructor
    · apply Measure.le_iff.mpr
      intro E _hE
      rw [Measure.smul_apply,smul_eq_mul]
      have h := mul_le_mul_of_nonneg_right
        (show ENNReal.ofReal (3/4)≤(1 : ENNReal) by norm_num) (show (0 : ENNReal)≤P.law j E from bot_le)
      simpa only [one_mul] using h
    · apply Measure.le_iff.mpr
      intro E _hE
      rw [Measure.smul_apply,smul_eq_mul]
      have h := mul_le_mul_of_nonneg_right
        (show (1 : ENNReal)≤ENNReal.ofReal (5/4) by norm_num) (show (0 : ENNReal)≤P.law j E from bot_le)
      simpa only [one_mul] using h


end ProphetSecretary.Limiting
