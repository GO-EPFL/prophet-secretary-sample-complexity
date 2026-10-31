import ProphetSecretary.Limiting.CountableWindowDurationScore
import ProphetSecretary.Limiting.CountableWindowScoreSum

/-!
# Complete duration scores on windows above the reserve

The complete score is the proved finite sum of construction-band scores.
Each summand is nonpositive for the fixed Markov rule. A zero total score
makes every contributing insertion decrease vanish; bands below the window
have zero window intensity. This covers arbitrary measurable positive
windows and includes all future points only as analytical score variables.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

theorem countableMarkovRule_poissonRegion_durationScore_nonpositive
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ)<b)
    {S : Set Point} (hS : MeasurableSet S) (hSub : S ⊆ univ ×ˢ Ioi b) :
    Integrable (fun v : CompleteWorld Seed => (countableMarkovRule accept).infimumDuration v*
        ((bandPointCount S v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real S)) (B.completeWorldLaw ν) ∧
      (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
        ((bandPointCount S v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real S) ∂B.completeWorldLaw ν) ≤ 0 := by
  obtain ⟨K,_hK,hSum⟩ := B.poissonRegionScore_eq_finite_sum ν hb hS hSub
  let L := Finset.range (K+1)
  have hLocal (k : ℕ) := countableMarkovRule_window_durationScore_nonpositive accept hπ B ν k S hS
  have hInt (k : ℕ) : Integrable (fun v : CompleteWorld Seed =>
      (countableMarkovRule accept).infimumDuration v*B.constructionWindowScore k S v) (B.completeWorldLaw ν) := (hLocal k).1
  have hAE : (fun v : CompleteWorld Seed => (countableMarkovRule accept).infimumDuration v*
      ((bandPointCount S v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real S)) =ᵐ[B.completeWorldLaw ν]
      (fun v => ∑ k ∈ L, (countableMarkovRule accept).infimumDuration v*B.constructionWindowScore k S v) := by
    filter_upwards [hSum] with v hv
    rw [hv,Finset.mul_sum]
  have hSumInt := integrable_finsetSum L (fun k _ => hInt k)
  refine ⟨hSumInt.congr hAE.symm,?_⟩
  rw [integral_congr_ae hAE,integral_finsetSum L (fun k _ => hInt k)]
  exact Finset.sum_nonpos (fun k _ => (hLocal k).2)

theorem countableMarkovRule_poissonRegion_insertion_eq_of_durationScore_zero
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ)<b)
    {S : Set Point} (hS : MeasurableSet S) (hSub : S ⊆ univ ×ˢ Ioi b)
    (hZero : (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      ((bandPointCount S v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real S) ∂B.completeWorldLaw ν)=0)
    (k : ℕ) :
    ∀ᵐ z : Point × CompleteWorld Seed
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν),
      z.1 ∈ S → (countableMarkovRule accept).insertionInfimumKernel k z=(countableMarkovRule accept).infimumDuration z.2 := by
  obtain ⟨K,hK,hSum⟩ := B.poissonRegionScore_eq_finite_sum ν hb hS hSub
  let L := Finset.range (K+1)
  by_cases hk : k ∈ L
  · have hLocal (j : ℕ) := countableMarkovRule_window_durationScore_nonpositive accept hπ B ν j S hS
    have hInt (j : ℕ) : Integrable (fun v : CompleteWorld Seed =>
        (countableMarkovRule accept).infimumDuration v*B.constructionWindowScore j S v) (B.completeWorldLaw ν) := (hLocal j).1
    have hAE : (fun v : CompleteWorld Seed => (countableMarkovRule accept).infimumDuration v*
        ((bandPointCount S v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real S)) =ᵐ[B.completeWorldLaw ν]
        (fun v => ∑ j ∈ L, (countableMarkovRule accept).infimumDuration v*B.constructionWindowScore j S v) := by
      filter_upwards [hSum] with v hv
      rw [hv,Finset.mul_sum]
    have hTotal : (∑ j ∈ L, ∫ v : CompleteWorld Seed,
        (countableMarkovRule accept).infimumDuration v*B.constructionWindowScore j S v ∂B.completeWorldLaw ν)=0 := by
      rw [← integral_finsetSum L (fun j _ => hInt j),← integral_congr_ae hAE]
      exact hZero
    have hEach := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => (hLocal j).2)).mp hTotal
    exact countableMarkovRule_window_insertion_eq_of_durationScore_zero accept hπ B ν k S hS (hEach k hk)
  · have hkg : K<k := by
      change k∉Finset.range (K+1) at hk
      simp only [Finset.mem_range,not_lt] at hk
      omega
    have hMass : (ProphetSecretary.Limiting.intensity (B.bandIntensity k)) S=0 := by
      apply measure_mono_null hSub
      simp only [ProphetSecretary.Limiting.intensity,Measure.prod_prod,B.bandIntensity_tail_zero hK k hkg,mul_zero]
    have hNot := (Measure.quasiMeasurePreserving_fst
      (μ := ProphetSecretary.Limiting.intensity (B.bandIntensity k)) (ν := B.completeWorldLaw ν)).ae
      (measure_eq_zero_iff_ae_notMem.mp hMass)
    filter_upwards [hNot] with z hz hPoint
    exact False.elim (hz hPoint)

end ProphetSecretary.Limiting.CountableInstance
