import ProphetSecretary.Model.RankRandomized
import ProphetSecretary.Model.Learner

/-!
# Adaptive learners with rank observations online

The sample requester observes only its seed and past training transcript.
The online callback observes that transcript and the current and past ranks,
identities and values. The hard reservoir budget holds on every outcome.
-/

open MeasureTheory

namespace ProphetSecretary.Model

structure RankLearner (n k : ℕ) where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  request : RequestRule n Seed
  measurable_request : MeasurableRequestRule request
  decide : Seed → Transcript n → Fin n → Fin n → ℝ → RankHistory n → Bool
  measurable_decide : Measurable (fun z :
      (Seed × Transcript n) × (Fin n × (Fin n × (ℝ × RankHistory n))) =>
    decide z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)

attribute [instance] RankLearner.seedSpace RankLearner.probability

namespace RankLearner

variable {n k : ℕ} (L : RankLearner n k)

def policy : RankPolicy (Reservoir n k × L.Seed) n where
  decide yr t i x H := L.decide yr.2 (trainingTranscript L.request yr.2 yr.1) t i x H

lemma policy_isMeasurable : L.policy.IsMeasurable := by
  let Ω := (Reservoir n k × L.Seed) × (Fin n × (Fin n × (ℝ × RankHistory n)))
  have hr : Measurable (fun z : Ω => z.1.2) := measurable_snd.comp measurable_fst
  have hy : Measurable (fun z : Ω => z.1.1) := measurable_fst.comp measurable_fst
  have hT := measurable_trainingTranscript L.request L.measurable_request hr hy
  exact L.measurable_decide.comp ((hr.prodMk hT).prodMk measurable_snd)

lemma hard_budget (r : L.Seed) (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript L.request r y) i ≤ k :=
  trainingTranscript_budget L.request r y i

noncomputable def randomizedPolicy (P : Instance n) : RandomizedRankPolicy n where
  Seed := Reservoir n k × L.Seed
  seedLaw := (P.reservoirLaw k).prod L.seedLaw
  rule := L.policy
  measurable_rule := L.policy_isMeasurable

noncomputable def expectedReward (P : Instance n) : ℝ :=
  (L.randomizedPolicy P).expectedReward P

noncomputable def reachProbability (P : Instance n) (i : Fin n) : ℝ :=
  ((L.randomizedPolicy P).worldLaw P).real {ω | L.policy.Reaches ω.2.2 ω.2.1 ω.1 i}

/-- The same learner must work for every instance law. -/
def Guarantees (rho : ℝ) : Prop :=
  ∀ P : Instance n, P.HasPositiveFiniteMaximum → rho*P.expectedMaximum ≤ L.expectedReward P

end RankLearner
end ProphetSecretary.Model
