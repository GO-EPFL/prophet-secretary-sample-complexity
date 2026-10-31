import ProphetSecretary.Model.RankToClockMeasurability
import ProphetSecretary.Model.RankRandomized

/-!
# Equality in law for rank-to-clock policy simulation

The adapter keeps the original auxiliary seed law. Erasing the numerical clocks
and retaining only their identity permutation has the actual independent uniform
rank-world law. This full permutation is an analytical world map, never callback
input. Expected reward and each reach probability are preserved; physical duration
is not identified with a rank observation.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def RandomizedRankPolicy.rankToClock (π : RandomizedRankPolicy n) : RandomizedPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.rankToClock
  measurable_rule := π.rule.rankToClock_measurable π.measurable_rule

namespace RandomizedRankPolicy
variable (π : RandomizedRankPolicy n)

noncomputable def reachProbability (P : Instance n) (i : Fin n) : ℝ :=
  (π.worldLaw P).real {ω | π.rule.Reaches ω.2.2 ω.2.1 ω.1 i}

noncomputable def clockWorldToRankWorld (ω : ProphetSecretary.Model.World n π.Seed) : π.World :=
  (ω.1,(Instance.arrivalPermutation ω.2.1,ω.2.2))

lemma clockWorldToRankWorld_measurePreserving (P : Instance n) :
    MeasurePreserving π.clockWorldToRankWorld (P.worldLaw π.seedLaw) (π.worldLaw P) := by
  have hPerm : MeasurePreserving (@Instance.arrivalPermutation n) (Instance.clocksLaw n) (Instance.uniformPermutationLaw n) :=
    ⟨Instance.measurable_arrivalPermutation,Instance.arrivalPermutation_map⟩
  exact (MeasurePreserving.id P.valuesLaw).prod (hPerm.prod (MeasurePreserving.id π.seedLaw))

lemma rankToClock_clocks_regular (P : Instance n) :
    ∀ᵐ ω : ProphetSecretary.Model.World n π.Seed ∂P.worldLaw π.seedLaw,
      Function.Injective ω.2.1 ∧ StrictMono (Instance.sortedClocks ω.2.1) ∧
        ∀ k, Instance.sortedClocks ω.2.1 k≤1 := by
  have h0 := measurePreserving_fst (μ:=Instance.clocksLaw n) (ν:=π.seedLaw)
  have h1 := measurePreserving_snd (μ:=P.valuesLaw) (ν:=(Instance.clocksLaw n).prod π.seedLaw)
  have hInj : ∀ᵐ ω : ProphetSecretary.Model.World n π.Seed ∂P.worldLaw π.seedLaw, Function.Injective ω.2.1 :=
    (h0.comp h1).quasiMeasurePreserving.ae (Instance.clocks_pairwise_distinct (n:=n))
  filter_upwards [hInj,P.world_clocks_mem_unitInterval π.seedLaw] with ω hI hU
  refine ⟨hI,?_,?_⟩
  · simpa only [Instance.sortedClocks,if_pos hI,Instance.HasArrivalOrder] using Instance.hasArrivalOrder_arrivalPermutation hI
  · intro k
    simpa only [Instance.sortedClocks,if_pos hI] using (hU (Instance.arrivalPermutation ω.2.1 k)).2

lemma rankToClock_reward_ae (P : Instance n) :
    (fun ω : ProphetSecretary.Model.World n π.Seed => π.rule.rankToClock.reward ω.2.2 Finset.univ ω.1 ω.2.1) =ᵐ[P.worldLaw π.seedLaw]
      (fun ω => π.realizedReward (π.clockWorldToRankWorld ω)) := by
  filter_upwards [π.rankToClock_clocks_regular P] with ω hω
  have h := π.rule.rankToClock_reward ω.2.2 (Instance.sortedClocks ω.2.1) hω.2.1 hω.2.2
    (Instance.arrivalPermutation ω.2.1) ω.1
  rw [Instance.reconstruct_sorted_arrivalPermutation hω.1] at h
  exact h

/-- The two rewards have genuine finite expectations whenever the benchmark is
integrable. Both integrability obligations are discharged in their original worlds. -/
lemma rankToClock_rewards_integrable (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable π.rankToClock.realizedReward (P.worldLaw π.seedLaw) ∧
      Integrable π.realizedReward (π.worldLaw P) :=
  ⟨π.rankToClock.integrable_realizedReward P hP,π.integrable_realizedReward P hP⟩

lemma rankToClock_expectedReward (P : Instance n) :
    π.rankToClock.expectedReward P=π.expectedReward P := by
  have hp := π.clockWorldToRankWorld_measurePreserving P
  have hMap := integral_map (μ:=P.worldLaw π.seedLaw) hp.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at hMap
  change (∫ ω : ProphetSecretary.Model.World n π.Seed, π.rule.rankToClock.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw)=_
  exact (integral_congr_ae (π.rankToClock_reward_ae P)).trans hMap.symm

lemma rankToClock_reaches_ae (P : Instance n) (i : Fin n) :
    {ω : ProphetSecretary.Model.World n π.Seed | π.rule.rankToClock.Reaches ω.2.2 ω.1 ω.2.1 i} =ᵐ[P.worldLaw π.seedLaw]
      π.clockWorldToRankWorld ⁻¹' {ω | π.rule.Reaches ω.2.2 ω.2.1 ω.1 i} := by
  filter_upwards [π.rankToClock_clocks_regular P] with ω hω
  have h := π.rule.rankToClock_reaches ω.2.2 (Instance.sortedClocks ω.2.1) hω.2.1 hω.2.2
    (Instance.arrivalPermutation ω.2.1) ω.1 i
  rw [Instance.reconstruct_sorted_arrivalPermutation hω.1] at h
  exact propext h

lemma rankToClock_reach_probability (P : Instance n) (i : Fin n) :
    π.rankToClock.rule.reachProbability P π.seedLaw i=π.reachProbability P i := by
  have hp := π.clockWorldToRankWorld_measurePreserving P
  have hm : MeasurableSet {ω : π.World | π.rule.Reaches ω.2.2 ω.2.1 ω.1 i} :=
    π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst) i
  change (P.worldLaw π.seedLaw).real {ω : ProphetSecretary.Model.World n π.Seed | π.rule.rankToClock.Reaches ω.2.2 ω.1 ω.2.1 i}=π.reachProbability P i
  rw [Measure.real,measure_congr (π.rankToClock_reaches_ae P i),hp.measure_preimage hm.nullMeasurableSet]
  rfl

end RandomizedRankPolicy
end ProphetSecretary.Model
