import ProphetSecretary.Limiting.HybridCutoffPayoff

/-!
# A cutoff below every actual anonymous mark leaves execution unchanged

The support property is derived from the constructed point-process law.
The equality is of actual rewards and durations of the same callback, rather
than an inference from equality of optimal scalar values.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma configurationAbove_eq_of_all_marks (b : ℝ) (ω : Configuration)
    (h : ∀ j : Fin ω.1, b<(ω.2 j).2) :
    configurationAbove b ω = configurationFiniteMeasure ω := by
  apply FiniteMeasure.toMeasure_injective
  rw [configurationAbove_coe,configurationFiniteMeasure_coe,
    restricted_countingMeasure _ (MeasurableSet.univ.prod measurableSet_Ioi)]
  unfold countingMeasure
  apply Finset.sum_congr rfl
  intro j _
  exact if_pos ⟨mem_univ _,h j⟩

lemma configurationAbove_eq_ae (μ : FiniteMeasure ℝ) {b : ℝ}
    (hμ : ∀ᵐ x ∂(μ:Measure ℝ), b<x) :
    ∀ᵐ ω ∂configurationLaw μ, configurationAbove b ω = configurationFiniteMeasure ω := by
  have hMark : ∀ᵐ p : Point ∂intensity μ, p∈univ ×ˢ Ioi b := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := Model.Instance.uniformClock) (ν := (μ:Measure ℝ))).ae hμ] with p hp
    exact ⟨mem_univ _,hp⟩
  filter_upwards [all_points_in_of_intensity_compl_null μ
    (MeasurableSet.univ.prod measurableSet_Ioi) (ae_iff.mp hMark)] with ω hω
  exact configurationAbove_eq_of_all_marks b ω (fun j => (hω j).2)

lemma HybridRule.above_payoffs_eq_ae (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ}
    (hHigh : ∀ᵐ x ∂(B.intensity:Measure ℝ), b<x) :
    ∀ᵐ v ∂B.law ν, (π.above b).realizedDuration v=π.realizedDuration v ∧
      (π.above b).realizedReward B.terminal v=π.realizedReward B.terminal v := by
  have hHighConfig : ∀ᵐ v ∂B.law ν, configurationAbove b v.1=configurationFiniteMeasure v.1 :=
    (measurePreserving_fst (μ := configurationLaw B.intensity) (ν := B.individuals.worldLaw ν)).quasiMeasurePreserving.ae
      (configurationAbove_eq_ae B.intensity hHigh)
  filter_upwards [hHighConfig,hybrid_combined_clocks_regular B.individuals B.intensity ν,
    realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported,
    π.hybrid_payoffs_eq_observable hπ B ν] with v hConfig hClock hValue hPay
  have hu (k) : combinedClocks v.2.2.1 v.1.2 k∈Icc (0:ℝ) 1 := ⟨(hClock.2 k).1.le,(hClock.2 k).2.le⟩
  have hObs : hybridObserverAbove b v=hybridObserverWorld v := Prod.ext hConfig rfl
  constructor
  · rw [← π.above_duration_eq_observable hπ b v hu,hObs,hPay.1]
  · rw [← π.above_reward_eq_observable hπ b v hu (fun k => (hValue k).1) hClock.1 B.terminal,hObs,hPay.2]
end ProphetSecretary.Limiting
