import ProphetSecretary.Limiting.CountableInsertionInfimumKernel

/-!
# Weighted one-point insertion kernels

A fixed measurable point weight in `[0,1]` restricts Mecke to any desired
part of a construction band. Indicator weights give positive mark windows.
Weights here are analytical functions of the complete marked points.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting

noncomputable def realPointSum (f : Point → ℝ) (ω : Configuration) : ℝ := ∑ j : Fin ω.1, f (ω.2 j)

lemma measurable_realPointSum (f : Point → ℝ) (hf : Measurable f) : Measurable (realPointSum f) := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun v : Fin N → Point => ∑ j : Fin N, f (v j))
  exact Finset.measurable_fun_sum _ (fun j _ => hf.comp (measurable_pi_apply j))

namespace CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def CountableRule.weightedInsertionInfimumKernel (π : CountableRule Seed)
    (k : ℕ) (f : Point → ℝ) (z : Point × CompleteWorld Seed) : ℝ :=
  f z.1*π.insertionInfimumKernel k z

lemma CountableRule.measurable_weightedInsertionInfimumKernel (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (k : ℕ) (f : Point → ℝ) (hf : Measurable f) : Measurable (π.weightedInsertionInfimumKernel k f) :=
  (hf.comp measurable_fst).mul (π.measurable_insertionInfimumKernel hπ k)

omit [MeasurableSpace Seed] in
lemma CountableRule.weightedInsertionInfimumKernel_bounds (π : CountableRule Seed)
    (k : ℕ) (f : Point → ℝ) (hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1) (z : Point × CompleteWorld Seed) :
    π.weightedInsertionInfimumKernel k f z ∈ Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg (hBound _).1 (π.insertionInfimumKernel_bounds k z).1,
    mul_le_one₀ (hBound _).2 (π.insertionInfimumKernel_bounds k z).1 (π.insertionInfimumKernel_bounds k z).2⟩

omit [MeasurableSpace Seed] in
lemma countableMarkovRule_realBandMeckeSum_weightedInsertionInfimum
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (k : ℕ) (f : Point → ℝ) (v : CompleteWorld Seed) :
    realBandMeckeSum k ((countableMarkovRule accept).weightedInsertionInfimumKernel k f) v=
      realPointSum f (v.1 k)*(countableMarkovRule accept).infimumDuration v := by
  unfold realBandMeckeSum CountableRule.weightedInsertionInfimumKernel CountableRule.insertionInfimumKernel
  simp_rw [countableMarkovRule_infimumDuration_append_erased]
  rw [← Finset.sum_mul]
  rfl

theorem countableMarkovRule_integral_weightedSum_mul_infimum_eq_insertion
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) (f : Point → ℝ)
    (hf : Measurable f) (hBound : ∀ p, f p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun v : CompleteWorld Seed => realPointSum f (v.1 k)*(countableMarkovRule accept).infimumDuration v)
        (B.completeWorldLaw ν) ∧
      (∫ v : CompleteWorld Seed, realPointSum f (v.1 k)*(countableMarkovRule accept).infimumDuration v ∂B.completeWorldLaw ν)=
        ∫ z, (countableMarkovRule accept).weightedInsertionInfimumKernel k f z
          ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν) := by
  have hMecke := B.band_mecke_real_bounded ν k _
    ((countableMarkovRule accept).measurable_weightedInsertionInfimumKernel hπ k f hf)
    ((countableMarkovRule accept).weightedInsertionInfimumKernel_bounds k f hBound)
  have hFunction : realBandMeckeSum k ((countableMarkovRule accept).weightedInsertionInfimumKernel k f)=
      (fun v : CompleteWorld Seed => realPointSum f (v.1 k)*(countableMarkovRule accept).infimumDuration v) :=
    funext (countableMarkovRule_realBandMeckeSum_weightedInsertionInfimum accept k f)
  rw [hFunction] at hMecke
  exact ⟨hMecke.1,hMecke.2.2⟩

end CountableInstance
end ProphetSecretary.Limiting
