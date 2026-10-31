import ProphetSecretary.Limiting.CountableBandScaling
import ProphetSecretary.Limiting.CountableInstance

/-!
# Fixed cutoffs and finite band perturbations

Band scaling commutes with restricting the mark intensity at a fixed cutoff.
On the quarter likelihood interval the finite scaled mass is at most 5/4
of its base mass, so fixed base virtual counts remain valid throughout the
perturbation neighborhood.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting

lemma CountableInstance.scaleBand_intensityAbove (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) (b : ℝ) (hb : (B.terminal:ℝ)<b) :
    (B.scaleBand S r).intensityAbove b hb=bandScaledIntensity (B.intensityAbove b hb) S r := by
  apply FiniteMeasure.toMeasure_injective
  rw [bandScaledIntensity_toMeasure _ hS r]
  change (B.intensity.withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x))).restrict (Ioi b)=
    (B.intensity.restrict (Ioi b)).withDensity (fun x => ENNReal.ofReal (bandScaleFactor S r x))
  exact restrict_withDensity measurableSet_Ioi _

lemma bandScaledIntensity_mass_le_quarter (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r:ℝ)=1+θ) :
    ((bandScaledIntensity μ S r).mass:ℝ)≤(5/4)*(μ.mass:ℝ) := by
  have hMass := bandScaledIntensity_mass_difference μ hS r
  have hBand : (μ S:ℝ)≤(μ.mass:ℝ) := measureReal_mono (μ := (μ:Measure ℝ)) (subset_univ S)
  have hPos : 0≤(μ S:ℝ) := NNReal.coe_nonneg _
  have hProd := mul_le_mul_of_nonneg_right (abs_le.mp hθ).2 hPos
  have hProd' := mul_le_mul_of_nonneg_left hBand (by norm_num : (0:ℝ)≤1/4)
  rw [hr] at hMass
  nlinarith only [hMass,hProd,hProd']
end ProphetSecretary.Limiting
