import ProphetSecretary.Limiting.CountableWeightedInsertionKernel

/-!
# Weighted Poisson duration scores

Fixed measurable point weights in `[0,1]` permit restriction to a desired
positive mark window. Weighted Mecke identifies the score with minus the
nonnegative weighted insertion decrease. Zero score therefore removes that
weighted decrease almost everywhere, with all integrability obligations
proved on the actual full product law.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

theorem countableMarkovRule_weighted_insertion_gain_integral
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) (f : Point → ℝ)
    (hf : Measurable f) (hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun v : CompleteWorld Seed => (countableMarkovRule accept).infimumDuration v*
        (realPointSum f (v.1 k)-(∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k)))) (B.completeWorldLaw ν) ∧
      Integrable (fun z : Point × CompleteWorld Seed => f z.1*(countableMarkovRule accept).infimumDuration z.2-
        (countableMarkovRule accept).weightedInsertionInfimumKernel k f z)
        ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) ∧
      (∫ z : Point × CompleteWorld Seed, f z.1*(countableMarkovRule accept).infimumDuration z.2-
        (countableMarkovRule accept).weightedInsertionInfimumKernel k f z
          ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν))=
      -(∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
        (realPointSum f (v.1 k)-(∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))) ∂B.completeWorldLaw ν) := by
  let π := countableMarkovRule accept
  let bandRate : ℝ := (∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))
  have hDInt := π.integrable_infimumDuration hπ B ν
  have hDm := π.measurable_infimumDuration hπ
  have hCount := countableMarkovRule_integral_weightedSum_mul_infimum_eq_insertion accept hπ B ν k f hf hBound
  have hBaseInt : Integrable (fun z : Point × CompleteWorld Seed => f z.1*π.infimumDuration z.2)
      ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) := by
    apply Integrable.of_bound ((hf.comp measurable_fst).mul (hDm.comp measurable_snd)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      change ‖f z.1*π.infimumDuration z.2‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hBound z.1).1 (π.infimumDuration_bounds z.2).1)]
      exact mul_le_one₀ (hBound z.1).2 (π.infimumDuration_bounds z.2).1 (π.infimumDuration_bounds z.2).2)
  have hInsertInt : Integrable (π.weightedInsertionInfimumKernel k f)
      ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) := by
    apply Integrable.of_bound (π.measurable_weightedInsertionInfimumKernel hπ k f hf).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (π.weightedInsertionInfimumKernel_bounds k f hBound z).1]
      exact (π.weightedInsertionInfimumKernel_bounds k f hBound z).2)
  have hBaseMean : (∫ z : Point × CompleteWorld Seed, f z.1*π.infimumDuration z.2
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν))=
      bandRate*(∫ v, π.infimumDuration v ∂B.completeWorldLaw ν) := by
    rw [integral_prod _ hBaseInt]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
  have hScoreInt : Integrable (fun v : CompleteWorld Seed => π.infimumDuration v*(realPointSum f (v.1 k)-bandRate))
      (B.completeWorldLaw ν) := by
    apply (hCount.1.sub (hDInt.const_mul bandRate)).congr
    exact Eventually.of_forall (fun v => by
      change realPointSum f (v.1 k)*π.infimumDuration v-bandRate*π.infimumDuration v=
        π.infimumDuration v*(realPointSum f (v.1 k)-bandRate)
      ring)
  have hScoreMean : (∫ v : CompleteWorld Seed, π.infimumDuration v*(realPointSum f (v.1 k)-bandRate) ∂B.completeWorldLaw ν)=
      (∫ v : CompleteWorld Seed, realPointSum f (v.1 k)*π.infimumDuration v ∂B.completeWorldLaw ν)-
        bandRate*(∫ v, π.infimumDuration v ∂B.completeWorldLaw ν) := by
    calc
      _ = ∫ v : CompleteWorld Seed, realPointSum f (v.1 k)*π.infimumDuration v-bandRate*π.infimumDuration v ∂B.completeWorldLaw ν := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun v => by ring)
      _ = _ := by
        rw [integral_sub hCount.1 (hDInt.const_mul bandRate),integral_const_mul]
  refine ⟨hScoreInt,hBaseInt.sub hInsertInt,?_⟩
  rw [integral_sub hBaseInt hInsertInt,hBaseMean,← hCount.2,hScoreMean]
  ring

theorem countableMarkovRule_weighted_durationScore_nonpositive
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) (f : Point → ℝ)
    (hf : Measurable f) (hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1) :
    (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      (realPointSum f (v.1 k)-(∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))) ∂B.completeWorldLaw ν)≤0 := by
  have hGain := countableMarkovRule_weighted_insertion_gain_integral accept hπ B ν k f hf hBound
  have hNonnegative : 0 ≤ ∫ z : Point × CompleteWorld Seed, f z.1*(countableMarkovRule accept).infimumDuration z.2-
      (countableMarkovRule accept).weightedInsertionInfimumKernel k f z
        ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν) :=
    integral_nonneg (fun z => sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (countableMarkovRule_infimumDuration_append_le accept k z.1 z.2) (hBound z.1).1))
  rw [hGain.2.2] at hNonnegative
  linarith

theorem countableMarkovRule_weighted_insertion_eq_of_durationScore_zero
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) (f : Point → ℝ)
    (hf : Measurable f) (hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1)
    (hZero : (∫ v : CompleteWorld Seed, (countableMarkovRule accept).infimumDuration v*
      (realPointSum f (v.1 k)-(∫ p, f p ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))) ∂B.completeWorldLaw ν)=0) :
    ∀ᵐ z : Point × CompleteWorld Seed
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν),
      (countableMarkovRule accept).weightedInsertionInfimumKernel k f z=f z.1*(countableMarkovRule accept).infimumDuration z.2 := by
  have hGain := countableMarkovRule_weighted_insertion_gain_integral accept hπ B ν k f hf hBound
  have hMean : (∫ z : Point × CompleteWorld Seed, f z.1*(countableMarkovRule accept).infimumDuration z.2-
      (countableMarkovRule accept).weightedInsertionInfimumKernel k f z
        ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν))=0 := by
    rw [hGain.2.2,hZero,neg_zero]
  have hNonneg (z : Point × CompleteWorld Seed) :
      0 ≤ f z.1*(countableMarkovRule accept).infimumDuration z.2-(countableMarkovRule accept).weightedInsertionInfimumKernel k f z :=
    sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (countableMarkovRule_infimumDuration_append_le accept k z.1 z.2) (hBound z.1).1)
  have hAE := (integral_eq_zero_iff_of_nonneg
    (f := fun z : Point × CompleteWorld Seed => f z.1*(countableMarkovRule accept).infimumDuration z.2-
      (countableMarkovRule accept).weightedInsertionInfimumKernel k f z) hNonneg hGain.2.1).mp hMean
  filter_upwards [hAE] with z hz
  exact (sub_eq_zero.mp hz).symm

end ProphetSecretary.Limiting.CountableInstance
