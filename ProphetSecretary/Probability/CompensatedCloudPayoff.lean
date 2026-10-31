import ProphetSecretary.Probability.ScorePayoffComparison
import ProphetSecretary.Probability.CompensatedCloudScore
import ProphetSecretary.Probability.IndependentBandCount

/-!
# Full-complement compensation and bounded payoff expectations

The finite cloud score compensates on the entire complement of the band.
Its actual L² count approximation controls every bounded payoff with
independent auxiliary randomness, including an online policy's reward or
elapsed duration as an analytical function of the complete vector.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

theorem compensatedCloudScore_payoff_error (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure Aux) [IsProbabilityMeasure ν] {B : Set ℝ} (hB : MeasurableSet B)
    (hp : ∀ i, (μ i).real B≤1/2) (g : (Fin n → ℝ) × Aux → ℝ) (hg : Measurable g)
    {D : ℝ} (hD : 0≤D) (hb : ∀ q, |g q|≤D) :
    |(∫ q, completeScore (fun i => compensatedBandScore (μ i) B) q.1*g q ∂(Measure.pi μ).prod ν)-
      ∫ q, centeredIndependentBandCount μ B q.1*g q ∂(Measure.pi μ).prod ν|≤
      Real.sqrt (D^2*(∑ i, ((μ i).real B)^2)) := by
  let s := fun i => compensatedBandScore (μ i) B
  have hm (i : Fin n) : Measurable (s i) := measurable_compensatedBandScore (μ i) hB
  have hsB (i : Fin n) : ∀ᵐ x ∂μ i, |s i x|≤1 := Eventually.of_forall
    (compensatedBandScore_abs_le_one (μ i) (hp i))
  have hs : MemLp (completeScore s) 2 (Measure.pi μ) :=
    (memLp_two_iff_integrable_sq (measurable_completeScore hm).aestronglyMeasurable).mpr
      (completeScore_integrable_pow μ s hm hsB 2)
  have ht := (centeredIndependentBandCount_moments μ hB).1
  have hDiff : (∫ x, (completeScore s x-centeredIndependentBandCount μ B x)^2 ∂Measure.pi μ)≤
      ∑ i, ((μ i).real B)^2 := by
    simpa only [centeredIndependentBandCount,countIn] using compensatedCloudScore_centeredCount_L2 μ hB hp
  exact score_payoff_difference_le_L2 (Measure.pi μ) ν (completeScore s) (centeredIndependentBandCount μ B)
    hs ht hDiff g hg hD hb
end ProphetSecretary.Probability
