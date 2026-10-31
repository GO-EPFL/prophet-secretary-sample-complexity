import ProphetSecretary.Limiting.WeakExcessLaws
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Added intensity and reserve shifts

The positive excess-intensity map is additive. It cannot increase the first
moment of a nonnegative added mark law. Ordered finite intensities are
represented by their actual nonnegative measure difference.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

lemma excessIntensity_add (μ ρ : FiniteMeasure ℝ) (a : ℝ) :
    excessIntensity (μ+ρ) a = excessIntensity μ a+excessIntensity ρ a := by
  apply FiniteMeasure.toMeasure_injective
  change (((μ : Measure ℝ)+(ρ : Measure ℝ)).map (Model.excessValueMap a)).restrict (Ioi 0) =
    ((μ : Measure ℝ).map (Model.excessValueMap a)).restrict (Ioi 0)+
      ((ρ : Measure ℝ).map (Model.excessValueMap a)).restrict (Ioi 0)
  rw [Measure.map_add _ _ (Model.measurable_excessValueMap a),Measure.restrict_add]

lemma excessIntensity_firstMoment_le (ρ : FiniteMeasure ℝ) (a H : ℝ≥0)
    (hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Icc (0 : ℝ) H) :
    (∫ x, x ∂(excessIntensity ρ a : Measure ℝ)) ≤ ∫ x, x ∂(ρ : Measure ℝ) := by
  have hI : Integrable id (ρ : Measure ℝ) := by
    apply Integrable.of_bound aestronglyMeasurable_id H
    exact hρ.mono fun x hx => by simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hn := Model.excessLaw_nonnegative (ρ : Measure ℝ) (hρ.mono fun _ hx => hx.1) (a : ℝ)
  have hP := positivePremium_eq_positiveRestriction (Model.excessLaw (ρ : Measure ℝ) a) 1 0 zero_le_one le_rfl
  unfold Model.positivePremium at hP
  simp only [one_mul,sub_zero] at hP
  have hEq : (∫ x, x ∂(excessIntensity ρ a : Measure ℝ)) = ∫ x, Model.excessValueMap a x ∂(ρ : Measure ℝ) := by
    have hMax : (fun x : ℝ => max x 0) =ᵐ[Model.excessLaw (ρ : Measure ℝ) a] fun x => x :=
      hn.mono fun _ hx => max_eq_left hx
    have hMaxR := ae_restrict_of_ae hMax (s := Ioi (0 : ℝ))
    rw [integral_congr_ae hMax,integral_congr_ae hMaxR] at hP
    change (∫ x, x ∂(Model.excessLaw (ρ : Measure ℝ) a).restrict (Ioi 0)) = _
    rw [← hP]
    exact integral_map (Model.measurable_excessValueMap a).aemeasurable aestronglyMeasurable_id
  rw [hEq]
  apply integral_mono (Model.integrable_excessValueMap (ρ : Measure ℝ) hI a.property) hI
  intro x
  change x-min (a : ℝ) (max x 0) ≤ x
  exact sub_le_self _ (le_min a.property (le_max_right _ _))

noncomputable def finiteIntensityDifference (ν μ : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  ⟨(ν : Measure ℝ)-(μ : Measure ℝ),isFiniteMeasure_of_le (ν : Measure ℝ) Measure.sub_le⟩

lemma finiteIntensityDifference_supported (ν μ : FiniteMeasure ℝ) {A : Set ℝ}
    (hν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ A) :
    ∀ᵐ x ∂(finiteIntensityDifference ν μ : Measure ℝ), x ∈ A := ae_mono Measure.sub_le hν

lemma add_finiteIntensityDifference (ν μ : FiniteMeasure ℝ) (h : (μ : Measure ℝ) ≤ (ν : Measure ℝ)) :
    μ+finiteIntensityDifference ν μ = ν := by
  apply FiniteMeasure.toMeasure_injective
  change (μ : Measure ℝ)+((ν : Measure ℝ)-(μ : Measure ℝ)) = (ν : Measure ℝ)
  rw [add_comm,Measure.sub_add_cancel_of_le h]

end ProphetSecretary.Limiting
