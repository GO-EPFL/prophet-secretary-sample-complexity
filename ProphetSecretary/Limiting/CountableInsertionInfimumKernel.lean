import ProphetSecretary.Limiting.CountableBandMeckeReal
import ProphetSecretary.Limiting.CountableAppendInfimum

/-!
# Duration insertion kernel in a finite Poisson construction band

Deleting and reinserting a distinguished point restores the Markov
accepted-time set. Real Mecke therefore identifies the expected count times
duration with the integral of the independently inserted-point duration.
The infimum functional is analytical on counterfactual configurations.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal
namespace ProphetSecretary.Limiting

lemma intensity_real_univ (μ : FiniteMeasure ℝ) :
    (intensity μ).real Set.univ=(μ.mass : ℝ) := by
  rw [intensity,← Set.univ_prod_univ,measureReal_prod_prod,probReal_univ,one_mul,
    measureReal_def,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]

namespace CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def CountableRule.insertionInfimumKernel (π : CountableRule Seed) (k : ℕ)
    (z : Point × CompleteWorld Seed) : ℝ :=
  π.infimumDuration (appendAnonymousPoint k z.1 z.2)

lemma CountableRule.measurable_insertionInfimumKernel (π : CountableRule Seed) (hπ : π.IsMeasurable) (k : ℕ) :
    Measurable (π.insertionInfimumKernel k) :=
  (π.measurable_infimumDuration hπ).comp ((measurable_appendAnonymousPoint k).comp measurable_swap)

omit [MeasurableSpace Seed] in
lemma CountableRule.insertionInfimumKernel_bounds (π : CountableRule Seed) (k : ℕ)
    (z : Point × CompleteWorld Seed) : π.insertionInfimumKernel k z ∈ Icc (0 : ℝ) 1 :=
  π.infimumDuration_bounds _

omit [MeasurableSpace Seed] in
lemma countableMarkovRule_realBandMeckeSum_insertionInfimum
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (v : CompleteWorld Seed) :
    realBandMeckeSum k ((countableMarkovRule accept).insertionInfimumKernel k) v=
      ((v.1 k).1 : ℝ)*(countableMarkovRule accept).infimumDuration v := by
  unfold realBandMeckeSum CountableRule.insertionInfimumKernel
  simp_rw [countableMarkovRule_infimumDuration_append_erased]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem countableMarkovRule_integral_count_mul_infimum_eq_insertion
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) :
    Integrable (fun v : CompleteWorld Seed => ((v.1 k).1 : ℝ)*(countableMarkovRule accept).infimumDuration v)
        (B.completeWorldLaw ν) ∧
      (∫ v : CompleteWorld Seed, ((v.1 k).1 : ℝ)*(countableMarkovRule accept).infimumDuration v ∂B.completeWorldLaw ν)=
        ∫ z, (countableMarkovRule accept).insertionInfimumKernel k z
          ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν) := by
  have hMecke := B.band_mecke_real_bounded ν k _
    ((countableMarkovRule accept).measurable_insertionInfimumKernel hπ k)
    ((countableMarkovRule accept).insertionInfimumKernel_bounds k)
  have hFunction : realBandMeckeSum k ((countableMarkovRule accept).insertionInfimumKernel k)=
      (fun v : CompleteWorld Seed => ((v.1 k).1 : ℝ)*(countableMarkovRule accept).infimumDuration v) :=
    funext (countableMarkovRule_realBandMeckeSum_insertionInfimum accept k)
  rw [hFunction] at hMecke
  exact ⟨hMecke.1,hMecke.2.2⟩

end CountableInstance
end ProphetSecretary.Limiting
