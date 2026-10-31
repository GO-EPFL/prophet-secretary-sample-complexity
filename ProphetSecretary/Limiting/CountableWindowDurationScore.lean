import ProphetSecretary.Limiting.CountableWeightedPoissonDurationScore
import ProphetSecretary.Limiting.PoissonCounts

/-!
# Duration scores for measurable windows inside construction bands

Indicator weights restrict the actual Mecke identity to any measurable
time/mark window. The centered window count includes points after stopping;
it is an analytical likelihood score. Its canonical specialization and the
finite sum over bands apply to positive mark windows.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting

lemma realPointSum_indicator_eq_pointCount (S : Set Point) (ω : Configuration) :
    realPointSum (S.indicator (fun _ => (1 : ℝ))) ω=(pointCount S ω : ℝ) := by
  simp only [realPointSum,pointCount,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω.2 j ∈ S <;> simp [Set.indicator,hj]

namespace CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

theorem countableMarkovRule_window_durationScore_nonpositive
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) (S : Set Point) (hS : MeasurableSet S) :
    Integrable (fun v : CompleteWorld Seed => (countableMarkovRule accept).infimumDuration v*
        ((pointCount S (v.1 k) : ℝ)-(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S)) (B.completeWorldLaw ν) ∧
      (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
        ((pointCount S (v.1 k) : ℝ)-(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S) ∂B.completeWorldLaw ν) ≤ 0 := by
  let f := S.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hS
  have hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1 := by
    intro p
    by_cases hp : p ∈ S <;> simp [f,hp]
  have hGain := countableMarkovRule_weighted_insertion_gain_integral accept hπ B ν k f hf hBound
  have hSign := countableMarkovRule_weighted_durationScore_nonpositive accept hπ B ν k f hf hBound
  have hMean : (∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))=
      (ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S := integral_indicator_one hS
  simp only [f,realPointSum_indicator_eq_pointCount] at hGain hSign
  rw [hMean] at hGain hSign
  exact ⟨hGain.1,hSign⟩

theorem countableMarkovRule_window_insertion_eq_of_durationScore_zero
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) (S : Set Point) (hS : MeasurableSet S)
    (hZero : (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      ((pointCount S (v.1 k) : ℝ)-(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S) ∂B.completeWorldLaw ν)=0) :
    ∀ᵐ z : Point × CompleteWorld Seed
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν),
      z.1 ∈ S → (countableMarkovRule accept).insertionInfimumKernel k z=(countableMarkovRule accept).infimumDuration z.2 := by
  let f := S.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hS
  have hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1 := by
    intro p
    by_cases hp : p ∈ S <;> simp [f,hp]
  have hMean : (∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))=
      (ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S := integral_indicator_one hS
  have hWeightedZero : (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      (realPointSum f (v.1 k)-(∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))) ∂B.completeWorldLaw ν)=0 := by
    rw [hMean]
    simpa only [f,realPointSum_indicator_eq_pointCount] using hZero
  have hAE := countableMarkovRule_weighted_insertion_eq_of_durationScore_zero accept hπ B ν k f hf hBound hWeightedZero
  filter_upwards [hAE] with z hz hPoint
  change f z.1*(countableMarkovRule accept).insertionInfimumKernel k z=
    f z.1*(countableMarkovRule accept).infimumDuration z.2 at hz
  simpa only [f,Set.indicator_of_mem hPoint,one_mul] using hz

end CountableInstance
end ProphetSecretary.Limiting
