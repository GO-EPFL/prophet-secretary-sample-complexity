import ProphetSecretary.Model.RankLearner
import ProphetSecretary.Model.ClockToRankLaw
import ProphetSecretary.Model.TrainingSeedTransport
import ProphetSecretary.Model.RankSeedTransport

/-!
# Causal rank simulation of an adaptive clock learner

The new independent seed adds sorted uniform times. The sample requester
uses only the old seed, so its entire transcript is unchanged on every raw
array. Online decisions supply virtual times for the current and past ranks.
No distribution law is used by the learner constructor.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ}

def Learner.transcriptPolicy (L : Learner n k) : Policy (L.Seed × Transcript n) n where
  decide rD t i x H := L.decide rD.1 rD.2 t i x H

lemma Learner.transcriptPolicy_measurable (L : Learner n k) : L.transcriptPolicy.IsMeasurable :=
  L.measurable_decide

lemma Learner.clockToRank_decide_measurable (L : Learner n k) : Measurable
    (fun z : (((Fin n → ℝ) × L.Seed) × Transcript n) × (Fin n × (Fin n × (ℝ × RankHistory n))) =>
      L.decide z.1.1.2 z.1.2 (z.1.1.1 z.2.1) z.2.2.1 z.2.2.2.1
        (fun j => (z.2.2.2.2 j).map (fun a => (z.1.1.1 a.1,a.2)))) := by
  have h := L.transcriptPolicy.clockToRank_measurable L.transcriptPolicy_measurable
  exact h.comp (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc (MeasurableEquiv.refl _)).measurable

noncomputable def Learner.clockToRank (L : Learner n k) : RankLearner n k where
  Seed := (Fin n → ℝ) × L.Seed
  seedLaw := (Instance.sortedTimesLaw n).prod L.seedLaw
  request := L.request.pullbackSeed Prod.snd
  measurable_request := measurableRequestRule_pullbackSeed L.request L.measurable_request measurable_snd
  decide sr D q i x H := L.decide sr.2 D (sr.1 q) i x
    (fun j => (H j).map (fun a => (sr.1 a.1,a.2)))
  measurable_decide := L.clockToRank_decide_measurable

lemma Learner.clockToRank_trainingTranscript (L : Learner n k) (s : Fin n → ℝ) (r : L.Seed)
    (y : Reservoir n k) :
    trainingTranscript L.clockToRank.request (s,r) y = trainingTranscript L.request r y :=
  trainingTranscript_pullbackSeed L.request Prod.snd (s,r) y

lemma Learner.clockToRank_hard_budget (L : Learner n k) (s : Fin n → ℝ) (r : L.Seed)
    (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript L.clockToRank.request (s,r) y) i ≤ k := by
  rw [L.clockToRank_trainingTranscript]
  exact L.hard_budget r y i

/-- Reordering independent seed components does not alter an observation. -/
def Learner.clockToRankSeed (L : Learner n k)
    (z : Reservoir n k × ((Fin n → ℝ) × L.Seed)) : (Fin n → ℝ) × (Reservoir n k × L.Seed) :=
  (z.2.1,(z.1,z.2.2))

lemma Learner.clockToRank_policy (L : Learner n k) :
    L.clockToRank.policy = L.policy.clockToRank.pullbackSeed L.clockToRankSeed := by
  change @RankPolicy.mk (Reservoir n k × ((Fin n → ℝ) × L.Seed)) n _ =
    @RankPolicy.mk (Reservoir n k × ((Fin n → ℝ) × L.Seed)) n _
  apply congrArg RankPolicy.mk
  funext yr q i x H
  rcases yr with ⟨y,s,r⟩
  change L.decide r (trainingTranscript L.clockToRank.request (s,r) y) (s q) i x _ =
    L.decide r (trainingTranscript L.request r y) (s q) i x _
  rw [L.clockToRank_trainingTranscript]
  rfl

lemma Learner.measurable_clockToRankSeed (L : Learner n k) : Measurable L.clockToRankSeed := by
  unfold clockToRankSeed
  fun_prop

lemma Learner.clockToRankSeed_measurePreserving (L : Learner n k) (P : Instance n) :
    MeasurePreserving L.clockToRankSeed
      ((P.reservoirLaw k).prod ((Instance.sortedTimesLaw n).prod L.seedLaw))
      ((Instance.sortedTimesLaw n).prod ((P.reservoirLaw k).prod L.seedLaw)) := by
  have h0 := (measurePreserving_prodAssoc (P.reservoirLaw k) (Instance.sortedTimesLaw n)
    L.seedLaw).symm MeasurableEquiv.prodAssoc
  have h1 := (Measure.measurePreserving_swap (μ := P.reservoirLaw k)
    (ν := Instance.sortedTimesLaw n)).prod (MeasurePreserving.id L.seedLaw)
  have h2 := measurePreserving_prodAssoc (Instance.sortedTimesLaw n) (P.reservoirLaw k) L.seedLaw
  exact h2.comp (h1.comp h0)

lemma Learner.clockToRank_expectedReward (L : Learner n k) (P : Instance n) :
    L.clockToRank.expectedReward P = L.expectedReward P := by
  let ν := (P.reservoirLaw k).prod ((Instance.sortedTimesLaw n).prod L.seedLaw)
  let π := (L.randomizedPolicy P).clockToRank
  have hLaw : MeasurePreserving L.clockToRankSeed ν π.seedLaw := L.clockToRankSeed_measurePreserving P
  calc
    L.clockToRank.expectedReward P =
        (π.pullbackSeed ν L.clockToRankSeed L.measurable_clockToRankSeed).expectedReward P := by
      change (∫ ω, L.clockToRank.policy.reward ω.2.2 ω.2.1 ω.1
          ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ν)) =
        ∫ ω, (L.policy.clockToRank.pullbackSeed L.clockToRankSeed).reward ω.2.2 ω.2.1 ω.1
          ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ν)
      rw [L.clockToRank_policy]
      rfl
    _ = π.expectedReward P := π.pullbackSeed_expectedReward ν L.clockToRankSeed
      L.measurable_clockToRankSeed hLaw P
    _ = L.expectedReward P := (L.randomizedPolicy P).clockToRank_expectedReward P

lemma Learner.clockToRank_reachProbability (L : Learner n k) (P : Instance n) (i : Fin n) :
    L.clockToRank.reachProbability P i = L.reachProbability P i := by
  let ν := (P.reservoirLaw k).prod ((Instance.sortedTimesLaw n).prod L.seedLaw)
  let π := (L.randomizedPolicy P).clockToRank
  have hLaw : MeasurePreserving L.clockToRankSeed ν π.seedLaw := L.clockToRankSeed_measurePreserving P
  calc
    L.clockToRank.reachProbability P i =
        ((π.pullbackSeed ν L.clockToRankSeed L.measurable_clockToRankSeed).worldLaw P).real
          {ω | (π.pullbackSeed ν L.clockToRankSeed L.measurable_clockToRankSeed).rule.Reaches
            ω.2.2 ω.2.1 ω.1 i} := by
      change (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ν)).real
          {ω | L.clockToRank.policy.Reaches ω.2.2 ω.2.1 ω.1 i} =
        (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ν)).real
          {ω | (L.policy.clockToRank.pullbackSeed L.clockToRankSeed).Reaches ω.2.2 ω.2.1 ω.1 i}
      rw [L.clockToRank_policy]
      rfl
    _ = (π.worldLaw P).real {ω | π.rule.Reaches ω.2.2 ω.2.1 ω.1 i} :=
      π.pullbackSeed_reach_probability ν L.clockToRankSeed L.measurable_clockToRankSeed hLaw P i
    _ = L.reachProbability P i := (L.randomizedPolicy P).clockToRank_reach_probability P i

lemma Learner.clockToRank_guarantees_iff (L : Learner n k) (rho : ℝ) :
    L.clockToRank.Guarantees rho ↔ L.Guarantees rho := by
  simp only [RankLearner.Guarantees,Learner.Guarantees,L.clockToRank_expectedReward]

end ProphetSecretary.Model
