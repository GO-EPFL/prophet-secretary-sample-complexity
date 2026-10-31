import ProphetSecretary.Limiting.FinitePoissonBandLikelihood
import ProphetSecretary.Limiting.PoissonVoid

/-!
# Null bands contribute no actual points or likelihood change
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

lemma bandScaledIntensity_of_null (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hNull : (μ : Measure ℝ) S=0) (r : ℝ≥0) : bandScaledIntensity μ S r=μ := by
  have hNo : ∀ᵐ x ∂(μ : Measure ℝ), x ∉ S := measure_eq_zero_iff_ae_notMem.mp hNull
  have hDensity : (fun x => ENNReal.ofReal (bandScaleFactor S r x)) =ᵐ[(μ : Measure ℝ)] (1 : ℝ → ℝ≥0∞) :=
    hNo.mono (fun x hx => by simp only [bandScaleFactor,if_neg hx,ENNReal.ofReal_one,Pi.one_apply])
  apply FiniteMeasure.toMeasure_injective
  rw [bandScaledIntensity_toMeasure μ hS r,withDensity_congr_ae hDensity,withDensity_one]

lemma pointCount_band_eq_zero_ae (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hNull : (μ : Measure ℝ) S=0) :
    ∀ᵐ ω ∂configurationLaw μ, pointCount (univ ×ˢ S) ω=0 := by
  have hRegion : MeasurableSet ((univ : Set ℝ) ×ˢ S) := MeasurableSet.univ.prod hS
  have hNullPoint : intensity μ (univ ×ˢ S)=0 := by
    rw [intensity,Measure.prod_prod,hNull,mul_zero]
  have hAvoid := all_points_in_of_intensity_compl_null μ hRegion.compl
    (by simpa only [compl_compl] using hNullPoint)
  exact hAvoid.mono (fun ω hω => (pointCount_eq_zero_iff (univ ×ˢ S) ω).mpr (fun j => hω j))

lemma bandPoissonLikelihood_of_null (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hNull : (μ : Measure ℝ) S=0) (r : ℝ≥0) :
    ∀ᵐ ω ∂configurationLaw μ, bandPoissonLikelihood μ S r ω=1 := by
  have hNullNN : μ S=0 := by
    change ((μ : Measure ℝ) S).toNNReal=0
    rw [hNull]
    rfl
  filter_upwards [pointCount_band_eq_zero_ae μ hS hNull] with ω hω
  rw [bandPoissonLikelihood_eq μ hS r ω,hNullNN,hω]
  simp

end ProphetSecretary.Limiting
