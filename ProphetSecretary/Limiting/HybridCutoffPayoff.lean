import ProphetSecretary.Limiting.HybridCutoffRule
import ProphetSecretary.Limiting.HybridObserverPayoff

/-!
# Exact execution of the anonymous-cutoff adapter

The accepted-point measure of the original callback on the retained high
points equals the actual finite adapter's accepted atoms. This proves reward
and duration identities from causal actions, including the zero-reward and
unit-duration convention when nothing is selected.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.acceptedPointMeasure_above_eq_adapter (π : HybridRule n Seed)
    (hπ : π.IsMeasurable) (b : ℝ) (v : HybridWorld n Seed) :
    (π.acceptedPointMeasure (hybridObserverAbove b v) : Measure Point) =
      ∑ k : Fin (n+v.1.1), if combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1 ∧
        ((π.above b).asFinitePolicy v.1.1).action v.2.2.2 Finset.univ
          (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k = true then
        Measure.dirac (combinedClocks v.2.2.1 v.1.2 k,combinedValues v.2.1 v.1.2 k) else 0 := by
  have hA : MeasurableSet {p : Point | π.anonymousMeasureAccepted (hybridObserverAbove b v) p} :=
    (π.measurableSet_anonymousMeasureAccepted hπ).preimage measurable_prodMk_left
  change (∑ i : Fin n, if π.individualMeasureAccepted (hybridObserverAbove b v) i then
    Measure.dirac (v.2.2.1 i,v.2.1 i) else 0) +
    (configurationAbove b v.1 : Measure Point).restrict
      {p | π.anonymousMeasureAccepted (hybridObserverAbove b v) p} = _
  rw [configurationAbove_coe,Measure.restrict_restrict hA,
    restricted_countingMeasure _ (hA.inter (MeasurableSet.univ.prod measurableSet_Ioi)),Fin.sum_univ_add]
  apply congrArg₂ (fun α β : Measure Point => α+β)
  · apply Finset.sum_congr rfl
    intro i _
    simp only [combinedClocks,combinedValues,Fin.addCases_left,HybridRule.individualMeasureAccepted]
    simp only [π.individualMeasureAction_above b v i]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    simp only [combinedClocks,combinedValues,Fin.addCases_right,mem_inter_iff,mem_setOf_eq,
      mem_prod,mem_univ,true_and,mem_Ioi,HybridRule.anonymousMeasureAccepted]
    rw [π.anonymousMeasureAction_above b v j]
    by_cases hx : b<(v.1.2 j).2 <;> simp [hx]

lemma HybridRule.acceptedPointMeasure_above_eq_finiteCode (π : HybridRule n Seed)
    (hπ : π.IsMeasurable) (b : ℝ) (v : HybridWorld n Seed)
    (hu : ∀ k, combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1) :
    (π.acceptedPointMeasure (hybridObserverAbove b v) : Measure Point) =
      FirstAcceptance.pointMeasure (FiniteFirstAcceptance.acceptedCode ((π.above b).asFinitePolicy v.1.1)
        v.2.2.2 Finset.univ (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2))
        (FiniteFirstAcceptance.timeCode (combinedClocks v.2.2.1 v.1.2))
        (FiniteFirstAcceptance.valueCode (combinedValues v.2.1 v.1.2)) () := by
  rw [π.acceptedPointMeasure_above_eq_adapter hπ b v,FiniteFirstAcceptance.pointMeasure_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hu k,true_and,Model.Policy.mem_accepted,Finset.mem_univ]

lemma HybridRule.above_duration_eq_observable (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (b : ℝ) (v : HybridWorld n Seed)
    (hu : ∀ k, combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1) :
    π.observableDuration (hybridObserverAbove b v) = (π.above b).realizedDuration v := by
  rw [HybridRule.observableDuration,π.acceptedPointMeasure_above_eq_finiteCode hπ b v hu]
  exact FiniteFirstAcceptance.pointMeasure_time_eq _ _ _ _ _ hu

lemma HybridRule.above_reward_eq_observable (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (b : ℝ) (v : HybridWorld n Seed)
    (hu : ∀ k, combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1)
    (hx : ∀ k, 0≤combinedValues v.2.1 v.1.2 k)
    (hinj : Function.Injective (combinedClocks v.2.2.1 v.1.2)) (a : ℝ) :
    π.observableReward a (hybridObserverAbove b v) = (π.above b).realizedReward a v := by
  unfold HybridRule.observableReward HybridRule.realizedReward HybridRule.reward HybridRule.HasSelection
  have he := FiniteFirstAcceptance.pointMeasure_reward_eq ((π.above b).asFinitePolicy v.1.1)
    v.2.2.2 Finset.univ (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
    (π.acceptedPointMeasure (hybridObserverAbove b v))
    (π.acceptedPointMeasure_above_eq_finiteCode hπ b v hu) hu hx hinj a
  split_ifs with hs
  · rw [if_pos hs] at he
    exact he
  · rw [if_neg hs] at he
    exact he
end ProphetSecretary.Limiting
