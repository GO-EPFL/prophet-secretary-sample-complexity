import ProphetSecretary.Model.RankRandomized

/-!
# Equality in law for the clock-to-rank policy simulation

The sorted numerical times are drawn as independent auxiliary randomness.
A separately uniform online permutation reconstructs independent uniform
physical clocks. The causal policy adapter therefore preserves actual expected
reward and each reach probability. Physical durations are not compared here.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

namespace Instance

noncomputable def sortedTimesLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (clocksLaw n).map sortedClocks

instance sortedTimesLaw_probability : IsProbabilityMeasure (sortedTimesLaw n) :=
  Measure.isProbabilityMeasure_map measurable_sortedClocks.aemeasurable

lemma sortedTimesLaw_regular : ∀ᵐ s ∂sortedTimesLaw n, StrictMono s ∧ ∀ k, s k ≤ 1 := by
  have hStrict : MeasurableSet {s : Fin n → ℝ | StrictMono s} := by
    change MeasurableSet {s : Fin n → ℝ | ∀ a b : Fin n, a < b → s a < s b}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro a
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro b
    by_cases hab : a < b
    · simpa only [hab,true_implies] using measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b)
    · simp [hab]
  have hUnit : MeasurableSet {s : Fin n → ℝ | ∀ k, s k ≤ 1} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => measurableSet_le (measurable_pi_apply k) measurable_const
  apply (ae_map_iff measurable_sortedClocks.aemeasurable (hStrict.inter hUnit)).mpr
  filter_upwards [clocks_pairwise_distinct (n := n),clocks_mem_unitInterval (n := n)] with u hu hU
  constructor
  · simpa only [sortedClocks,if_pos hu,HasArrivalOrder,Set.mem_setOf_eq] using hasArrivalOrder_arrivalPermutation hu
  · intro k
    simpa only [sortedClocks,if_pos hu] using (hU (arrivalPermutation u k)).2

end Instance

noncomputable def RandomizedPolicy.clockToRank (π : RandomizedPolicy n) : RandomizedRankPolicy n where
  Seed := (Fin n → ℝ) × π.Seed
  seedLaw := (Instance.sortedTimesLaw n).prod π.seedLaw
  rule := π.rule.clockToRank
  measurable_rule := π.rule.clockToRank_measurable π.measurable_rule

namespace RandomizedPolicy

variable (π : RandomizedPolicy n)

/-- This map is analytical. Its full permutation argument is not supplied to
the rank policy's callback. -/
def clockToRankWorld (ω : π.clockToRank.World) : π.World :=
  (ω.1,(Instance.reconstructClocks (ω.2.2.1,ω.2.1),ω.2.2.2))

lemma clockToRankWorld_measurePreserving (P : Instance n) :
    MeasurePreserving π.clockToRankWorld (π.clockToRank.worldLaw P) (P.worldLaw π.seedLaw) := by
  have h0 := (measurePreserving_prodAssoc (Instance.uniformPermutationLaw n)
    (Instance.sortedTimesLaw n) π.seedLaw).symm MeasurableEquiv.prodAssoc
  have h1 := (Measure.measurePreserving_swap (μ := Instance.uniformPermutationLaw n)
    (ν := Instance.sortedTimesLaw n)).prod (MeasurePreserving.id π.seedLaw)
  haveI : IsProbabilityMeasure ((Instance.clocksLaw n).map Instance.sortedClocks) :=
    Measure.isProbabilityMeasure_map Instance.measurable_sortedClocks.aemeasurable
  have h2 := (Instance.reconstructClocks_measurePreserving (n := n)).prod (MeasurePreserving.id π.seedLaw)
  exact (MeasurePreserving.id P.valuesLaw).prod (h2.comp (h1.comp h0))

lemma clockToRank_sortedTimes_regular (P : Instance n) :
    ∀ᵐ ω ∂π.clockToRank.worldLaw P, StrictMono ω.2.2.1 ∧ ∀ k, ω.2.2.1 k ≤ 1 := by
  have h0 := measurePreserving_fst (μ := Instance.sortedTimesLaw n) (ν := π.seedLaw)
  have h1 := measurePreserving_snd (μ := Instance.uniformPermutationLaw n)
    (ν := (Instance.sortedTimesLaw n).prod π.seedLaw)
  have h2 := measurePreserving_snd (μ := P.valuesLaw)
    (ν := (Instance.uniformPermutationLaw n).prod ((Instance.sortedTimesLaw n).prod π.seedLaw))
  have hp : MeasurePreserving (fun ω : π.clockToRank.World => ω.2.2.1)
      (π.clockToRank.worldLaw P) (Instance.sortedTimesLaw n) := h0.comp (h1.comp h2)
  exact hp.quasiMeasurePreserving.ae Instance.sortedTimesLaw_regular

lemma clockToRank_reward_ae (P : Instance n) :
    π.clockToRank.realizedReward =ᵐ[π.clockToRank.worldLaw P]
      (fun ω => π.realizedReward (π.clockToRankWorld ω)) := by
  filter_upwards [π.clockToRank_sortedTimes_regular P] with ω hω
  exact π.rule.clockToRank_reward ω.2.2.2 ω.2.2.1 hω.1 hω.2 ω.2.1 ω.1

lemma clockToRank_expectedReward (P : Instance n) :
    π.clockToRank.expectedReward P = π.expectedReward P := by
  have hp := π.clockToRankWorld_measurePreserving P
  have hInt := integral_map (μ := π.clockToRank.worldLaw P) hp.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at hInt
  exact (integral_congr_ae (π.clockToRank_reward_ae P)).trans hInt.symm

lemma clockToRank_reaches_ae (P : Instance n) (i : Fin n) :
    {ω : π.clockToRank.World | π.clockToRank.rule.Reaches ω.2.2 ω.2.1 ω.1 i} =ᵐ[π.clockToRank.worldLaw P]
      π.clockToRankWorld ⁻¹' {ω | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i} := by
  filter_upwards [π.clockToRank_sortedTimes_regular P] with ω hω
  exact propext (π.rule.clockToRank_reaches ω.2.2.2 ω.2.2.1 hω.1 hω.2 ω.2.1 ω.1 i)

lemma clockToRank_reach_probability (P : Instance n) (i : Fin n) :
    (π.clockToRank.worldLaw P).real {ω | π.clockToRank.rule.Reaches ω.2.2 ω.2.1 ω.1 i} =
      (P.worldLaw π.seedLaw).real {ω | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i} := by
  have hp := π.clockToRankWorld_measurePreserving P
  have hm : MeasurableSet {ω : π.World | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i} :=
    π.rule.measurableSet_reaches π.measurable_rule
    (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  rw [Measure.real,measure_congr (π.clockToRank_reaches_ae P i),hp.measure_preimage hm.nullMeasurableSet]
  rfl

end RandomizedPolicy
end ProphetSecretary.Model
