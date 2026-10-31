import ProphetSecretary.Limiting.CountableInsertionInfimumKernel

/-!
# Poisson duration scores and the effect of one inserted point

For a fixed Markov rule the centered count score equals minus the integral
of the nonnegative duration decrease caused by inserting one point. Hence
the score is nonpositive, and a zero score makes that decrease vanish almost
everywhere. Integrability is proved from the actual finite band count and
the unit bound for duration; no optimizer derivative is used here.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

theorem countableMarkovRule_insertion_gain_integral
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) :
    Integrable (fun v : CompleteWorld Seed => (countableMarkovRule accept).infimumDuration v*
        (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass)) (B.completeWorldLaw ν) ∧
      Integrable (fun z : Point × CompleteWorld Seed => (countableMarkovRule accept).infimumDuration z.2-
        (countableMarkovRule accept).insertionInfimumKernel k z)
        ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) ∧
      (∫ z : Point × CompleteWorld Seed, (countableMarkovRule accept).infimumDuration z.2-
        (countableMarkovRule accept).insertionInfimumKernel k z
          ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν))=
      -(∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
        (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass) ∂B.completeWorldLaw ν) := by
  let π := countableMarkovRule accept
  let bandRate : ℝ := (B.bandIntensity k).mass
  have hDInt := π.integrable_infimumDuration hπ B ν
  have hDm := π.measurable_infimumDuration hπ
  have hCount := countableMarkovRule_integral_count_mul_infimum_eq_insertion accept hπ B ν k
  have hBaseInt : Integrable (fun z : Point × CompleteWorld Seed => π.infimumDuration z.2)
      ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) := by
    apply Integrable.of_bound (hDm.comp measurable_snd).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      change ‖π.infimumDuration z.2‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (π.infimumDuration_bounds z.2).1]
      exact (π.infimumDuration_bounds z.2).2)
  have hInsertInt : Integrable (π.insertionInfimumKernel k)
      ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) := by
    apply Integrable.of_bound (π.measurable_insertionInfimumKernel hπ k).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (π.insertionInfimumKernel_bounds k z).1]
      exact (π.insertionInfimumKernel_bounds k z).2)
  have hBaseMean : (∫ z : Point × CompleteWorld Seed, π.infimumDuration z.2
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν))=
      bandRate*(∫ v, π.infimumDuration v ∂B.completeWorldLaw ν) := by
    rw [integral_prod _ hBaseInt]
    simp only [integral_const,smul_eq_mul,intensity_real_univ,bandRate]
  have hScoreInt : Integrable (fun v : CompleteWorld Seed => π.infimumDuration v*(((v.1 k).1 : ℝ)-bandRate))
      (B.completeWorldLaw ν) := by
    apply (hCount.1.sub (hDInt.const_mul bandRate)).congr
    exact Eventually.of_forall (fun v => by
      change ((v.1 k).1 : ℝ)*π.infimumDuration v-bandRate*π.infimumDuration v=
        π.infimumDuration v*(((v.1 k).1 : ℝ)-bandRate)
      ring)
  have hScoreMean : (∫ v : CompleteWorld Seed, π.infimumDuration v*(((v.1 k).1 : ℝ)-bandRate) ∂B.completeWorldLaw ν)=
      (∫ v : CompleteWorld Seed, ((v.1 k).1 : ℝ)*π.infimumDuration v ∂B.completeWorldLaw ν)-
        bandRate*(∫ v, π.infimumDuration v ∂B.completeWorldLaw ν) := by
    calc
      _ = ∫ v : CompleteWorld Seed, ((v.1 k).1 : ℝ)*π.infimumDuration v-bandRate*π.infimumDuration v ∂B.completeWorldLaw ν := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun v => by ring)
      _ = _ := by
        rw [integral_sub hCount.1 (hDInt.const_mul bandRate),integral_const_mul]
  refine ⟨hScoreInt,hBaseInt.sub hInsertInt,?_⟩
  rw [integral_sub hBaseInt hInsertInt,hBaseMean,← hCount.2,hScoreMean]
  ring

theorem countableMarkovRule_durationScore_nonpositive
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) :
    (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass) ∂B.completeWorldLaw ν)≤0 := by
  have hGain := countableMarkovRule_insertion_gain_integral accept hπ B ν k
  have hNonnegative : 0 ≤ ∫ z : Point × CompleteWorld Seed, (countableMarkovRule accept).infimumDuration z.2-
      (countableMarkovRule accept).insertionInfimumKernel k z
        ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν) :=
    integral_nonneg (fun z => sub_nonneg.mpr (countableMarkovRule_infimumDuration_append_le accept k z.1 z.2))
  rw [hGain.2.2] at hNonnegative
  linarith

theorem countableMarkovRule_insertionInfimum_eq_of_durationScore_zero
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ)
    (hZero : (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass) ∂B.completeWorldLaw ν)=0) :
    ∀ᵐ z : Point × CompleteWorld Seed
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν),
      (countableMarkovRule accept).insertionInfimumKernel k z=(countableMarkovRule accept).infimumDuration z.2 := by
  have hGain := countableMarkovRule_insertion_gain_integral accept hπ B ν k
  have hMean : (∫ z : Point × CompleteWorld Seed, (countableMarkovRule accept).infimumDuration z.2-
      (countableMarkovRule accept).insertionInfimumKernel k z
        ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν))=0 := by
    rw [hGain.2.2,hZero,neg_zero]
  have hNonneg (z : Point × CompleteWorld Seed) :
      0 ≤ (countableMarkovRule accept).infimumDuration z.2-(countableMarkovRule accept).insertionInfimumKernel k z :=
    sub_nonneg.mpr (countableMarkovRule_infimumDuration_append_le accept k z.1 z.2)
  have hAE := (integral_eq_zero_iff_of_nonneg
    (f := fun z : Point × CompleteWorld Seed => (countableMarkovRule accept).infimumDuration z.2-
      (countableMarkovRule accept).insertionInfimumKernel k z) hNonneg hGain.2.1).mp hMean
  filter_upwards [hAE] with z hz
  exact (sub_eq_zero.mp hz).symm

end ProphetSecretary.Limiting.CountableInstance
