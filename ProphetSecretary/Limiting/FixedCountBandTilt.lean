import ProphetSecretary.Limiting.DirectScoreMarginals
import ProphetSecretary.Limiting.FiniteBandScalingReal
import ProphetSecretary.Probability.BandScorePositiveSets
import ProphetSecretary.Probability.NonnegativeTailExt

/-!
# The actual zero-atom tilt is the scaled-intensity design at the same count

Both marginal laws use the same fixed N. Positive sets have exactly the
scaled intensity divided by N; probability normalization and nonnegativity
then identify the full law, including its zero atom. No zero observation is
discarded in this identification.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

 theorem directPoissonMarginal_bandScore_tilt_eq
    (μ : FiniteMeasure ℝ) (H : ℝ≥0) (hSupport : ∀ᵐ x ∂(μ:Measure ℝ), x∈Ioc (0:ℝ) H)
    {B : Set ℝ} (hB : MeasurableSet B) (hB0 : (0:ℝ)∉B)
    (N : ℕ) (p pθ : unitInterval) (hp : (p:ℝ)=(μ.mass:ℝ)/(N:ℝ)) (hSmall : (p:ℝ)≤1/2)
    {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r:ℝ)=1+θ)
    (hpθ : (pθ:ℝ)=((bandScaledIntensity μ B r).mass:ℝ)/(N:ℝ)) :
    let κ := zeroInflatedLaw (normalizedMarkOrZero μ) p
    tiltLaw κ (bandScore κ B) θ=zeroInflatedLaw (normalizedMarkOrZero (bandScaledIntensity μ B r)) pθ := by
  let κ := zeroInflatedLaw (normalizedMarkOrZero μ) p
  let ν := bandScaledIntensity μ B r
  let η := zeroInflatedLaw (normalizedMarkOrZero ν) pθ
  have hκ : ∀ᵐ x ∂κ, 0≤x := zeroInflatedLaw_nonnegative _
    ((normalizedMarkOrZero_bounds μ H.property hSupport).mono (fun _ hx => hx.1)) p
  have hν : ∀ᵐ x ∂(ν:Measure ℝ), x∈Ioc (0:ℝ) H := by
    change ∀ᵐ x ∂(bandScaledIntensity μ B r:Measure ℝ), x∈Ioc (0:ℝ) H
    rw [bandScaledIntensity_toMeasure μ hB r]
    exact (withDensity_absolutelyContinuous _ _).ae_le hSupport
  have hη : ∀ᵐ x ∂η, 0≤x := zeroInflatedLaw_nonnegative _
    ((normalizedMarkOrZero_bounds ν H.property hν).mono (fun _ hx => hx.1)) pθ
  have hq : (1/2:ℝ)≤κ.real {0} := directPoissonMarginal_zero_mass_ge_half μ p hSmall
  have hsM := measurable_bandScore κ hB
  have hsB : ∀ᵐ x ∂κ, |bandScore κ B x|≤1 := Filter.Eventually.of_forall (bandScore_abs_le_one κ hB0 hq)
  haveI := tiltLaw_probability hsM hsB (bandScore_mean κ hB hq) hθ
  apply measure_eq_of_nonnegative_real_upper_tails (tiltLaw κ (bandScore κ B) θ) η
    ((tiltLaw_absolutelyContinuous κ (bandScore κ B) θ).ae_le hκ) hη
  intro x hx
  have hS0 : (0:ℝ)∉Ioi x := not_lt.mpr hx
  have hBase : κ.real (Ioi x)=(μ:Measure ℝ).real (Ioi x)/(N:ℝ) :=
    directPoissonMarginal_band_mass μ p N hp measurableSet_Ioi hS0
  have hBaseB : κ.real (Ioi x∩B)=(μ:Measure ℝ).real (Ioi x∩B)/(N:ℝ) :=
    directPoissonMarginal_band_mass μ p N hp (measurableSet_Ioi.inter hB) (fun h => hS0 h.1)
  have hTarget : η.real (Ioi x)=(ν:Measure ℝ).real (Ioi x)/(N:ℝ) :=
    directPoissonMarginal_band_mass ν pθ N hpθ measurableSet_Ioi hS0
  have hIntensity : (ν:Measure ℝ).real (Ioi x)=
      (μ:Measure ℝ).real (Ioi x)+θ*(μ:Measure ℝ).real (Ioi x∩B) := by
    calc
      _ = (μ:Measure ℝ).real (Ioi x)+((r:ℝ)-1)*(μ:Measure ℝ).real (Ioi x∩B) :=
        bandScaledIntensity_real_apply μ hB measurableSet_Ioi r
      _ = _ := by rw [hr];ring
  rw [bandScore_tilt_real_of_notMem_zero κ hB hB0 measurableSet_Ioi hS0 hq hθ,
    hBase,hBaseB,hTarget,hIntensity]
  ring
end ProphetSecretary.Limiting
