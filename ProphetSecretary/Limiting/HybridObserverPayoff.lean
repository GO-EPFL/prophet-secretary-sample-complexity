import ProphetSecretary.Limiting.HybridAcceptedMeasure
import ProphetSecretary.Limiting.FiniteFirstAcceptance
import ProphetSecretary.Limiting.CountableObserverPayoff
import ProphetSecretary.Limiting.HybridClockNullSets

/-!
# Actual finite hybrid payoffs from the common observer input

The finite adapter's accepted atoms equal the label-free observer measure.
The actual independent clocks are distinct, so its first slice is the single
selected occurrence. This proves reward and duration transport for every
measurable hybrid policy, without conditioning decisions on the total count.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.acceptedPointMeasure_eq_finiteCode (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (v : HybridWorld n Seed) (hu : ∀ k, combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1) :
    (π.acceptedPointMeasure (hybridObserverWorld v) : Measure Point) =
      FirstAcceptance.pointMeasure (FiniteFirstAcceptance.acceptedCode (π.asFinitePolicy v.1.1)
        v.2.2.2 Finset.univ (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2))
        (FiniteFirstAcceptance.timeCode (combinedClocks v.2.2.1 v.1.2))
        (FiniteFirstAcceptance.valueCode (combinedValues v.2.1 v.1.2)) () := by
  rw [π.acceptedPointMeasure_eq_adapter hπ v,FiniteFirstAcceptance.pointMeasure_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hu k,true_and,Model.Policy.mem_accepted,Finset.mem_univ]

lemma HybridRule.hybridDuration_eq_observable (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (v : HybridWorld n Seed) (hu : ∀ k, combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1) :
    π.observableDuration (hybridObserverWorld v) = π.realizedDuration v := by
  rw [HybridRule.observableDuration,π.acceptedPointMeasure_eq_finiteCode hπ v hu]
  exact FiniteFirstAcceptance.pointMeasure_time_eq _ _ _ _ _ hu

lemma HybridRule.hybridReward_eq_observable (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (v : HybridWorld n Seed) (hu : ∀ k, combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1)
    (hx : ∀ k, 0 ≤ combinedValues v.2.1 v.1.2 k)
    (hinj : Function.Injective (combinedClocks v.2.2.1 v.1.2)) (a : ℝ) :
    π.observableReward a (hybridObserverWorld v) = π.realizedReward a v := by
  unfold HybridRule.observableReward HybridRule.realizedReward HybridRule.reward HybridRule.HasSelection
  have he := FiniteFirstAcceptance.pointMeasure_reward_eq (π.asFinitePolicy v.1.1) v.2.2.2 Finset.univ
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
    (π.acceptedPointMeasure (hybridObserverWorld v)) (π.acceptedPointMeasure_eq_finiteCode hπ v hu) hu hx hinj a
  split_ifs with hs
  · rw [if_pos hs] at he
    exact he
  · rw [if_neg hs] at he
    exact he

lemma HybridRule.hybrid_payoffs_eq_observable (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.law ν,
      π.observableDuration (hybridObserverWorld v) = π.realizedDuration v ∧
      π.observableReward B.terminal (hybridObserverWorld v) = π.realizedReward B.terminal v := by
  have hclock := hybrid_combined_clocks_regular B.individuals B.intensity ν
  have hvalue := realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported
  filter_upwards [hclock,hvalue] with v hc hv
  have hu (k) : combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1 := ⟨(hc.2 k).1.le,(hc.2 k).2.le⟩
  exact ⟨π.hybridDuration_eq_observable hπ v hu,
    π.hybridReward_eq_observable hπ v hu (fun k => (hv k).1) hc.1 B.terminal⟩

lemma RandomizedHybridPolicy.expectedDuration_observable (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) :
    (∫ q, π.rule.observableDuration q ∂finiteObserverLaw B.individuals B.intensity π.seedLaw) = π.expectedDuration B := by
  have hmp := hybrid_finiteObserver_measurePreserving B.individuals B.intensity π.seedLaw
  have he := integral_map (μ := hybridWorldLaw B.individuals B.intensity π.seedLaw) hmp.measurable.aemeasurable
    (π.rule.measurable_observableDuration π.measurable_rule).aestronglyMeasurable
  rw [hmp.map_eq] at he
  have hpay := π.rule.hybrid_payoffs_eq_observable π.measurable_rule B π.seedLaw
  exact he.trans (integral_congr_ae (hpay.mono (fun _ h => h.1)))

lemma RandomizedHybridPolicy.expectedReward_observable (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) :
    (∫ q, π.rule.observableReward B.terminal q ∂finiteObserverLaw B.individuals B.intensity π.seedLaw) = π.expectedReward B := by
  have hmp := hybrid_finiteObserver_measurePreserving B.individuals B.intensity π.seedLaw
  have he := integral_map (μ := hybridWorldLaw B.individuals B.intensity π.seedLaw) hmp.measurable.aemeasurable
    (π.rule.measurable_observableReward π.measurable_rule B.terminal).aestronglyMeasurable
  rw [hmp.map_eq] at he
  have hpay := π.rule.hybrid_payoffs_eq_observable π.measurable_rule B π.seedLaw
  exact he.trans (integral_congr_ae (hpay.mono (fun _ h => h.2)))

end ProphetSecretary.Limiting
