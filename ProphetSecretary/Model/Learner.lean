import ProphetSecretary.Reach.FiniteReach
import ProphetSecretary.Model.TrainingExecution
import ProphetSecretary.Model.TrainingLaw
import ProphetSecretary.Model.CompetitiveBasic
import Mathlib.Data.ENat.Lattice

/-!
# Learners and sample complexity

One learner uses the same request and decision functions for every product law. Its seed
and training reservoir are independent of the online offers and clocks. All auxiliary
randomness may be drawn before training and included in the seed. The expected guarantee
averages over this seed, the training sample, and the online experiment; the sampling budget
holds for every seed and reservoir, independently of that expectation.
-/

open MeasureTheory

namespace ProphetSecretary.Model

/-- A measurable adaptive learner with a hard per-distribution reservoir budget `k`. -/
structure Learner (n k : ℕ) where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  request : RequestRule n Seed
  measurable_request : MeasurableRequestRule request
  decide : Seed → Transcript n → ℝ → Fin n → ℝ → History n → Bool
  measurable_decide : Measurable (fun z :
      (Seed × Transcript n) × (ℝ × (Fin n × (ℝ × History n))) =>
    decide z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)

attribute [instance] Learner.seedSpace Learner.probability

namespace Learner

variable {n k : ℕ} (L : Learner n k)

/-- The online policy receives the realized training data and independent seed. -/
def policy : Policy (Reservoir n k × L.Seed) n where
  decide y t i x h :=
    L.decide y.2 (trainingTranscript L.request y.2 y.1) t i x h

/-- Adaptivity preserves measurability of the induced online decision rule. -/
theorem policy_isMeasurable : L.policy.IsMeasurable := by
  let Ω := (Reservoir n k × L.Seed) × (ℝ × (Fin n × (ℝ × History n)))
  have hr : Measurable (fun z : Ω => z.1.2) := measurable_snd.comp measurable_fst
  have hs : Measurable (fun z : Ω => z.1.1) := measurable_fst.comp measurable_fst
  have ht := measurable_trainingTranscript L.request L.measurable_request hr hs
  exact L.measurable_decide.comp ((hr.prodMk ht).prodMk measurable_snd)

/-- The training budget holds on every outcome, including outcomes of probability zero. -/
theorem hard_budget (seed : L.Seed) (samples : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript L.request seed samples) i ≤ k :=
  trainingTranscript_budget L.request seed samples i

/-- The law, rather than the algorithm, supplies training samples from the unknown instance. -/
noncomputable def randomizedPolicy (P : Instance n) : RandomizedPolicy n where
  Seed := Reservoir n k × L.Seed
  seedLaw := (P.reservoirLaw k).prod L.seedLaw
  rule := L.policy
  measurable_rule := L.policy_isMeasurable

/-- The learner's expected reward, averaging over training and all online randomness. -/
noncomputable def expectedReward (P : Instance n) : ℝ :=
  (L.randomizedPolicy P).expectedReward P

/-- Reach also averages over the training experiment and independent policy seed. -/
noncomputable def reachProbability (P : Instance n) (i : Fin n) : ℝ :=
  L.policy.reachProbability P ((P.reservoirLaw k).prod L.seedLaw) i

noncomputable def meanDuration (P : Instance n) : ℝ :=
  L.policy.meanDuration P ((P.reservoirLaw k).prod L.seedLaw)

lemma reachProbability_nonnegative (P : Instance n) (i : Fin n) :
    0 ≤ L.reachProbability P i := ENNReal.toReal_nonneg

lemma reachProbability_le_twice_meanDuration (P : Instance n) (i : Fin n) :
    L.reachProbability P i ≤ 2 * L.meanDuration P :=
  L.policy.reachProbability_le_twice_meanDuration L.policy_isMeasurable P
    ((P.reservoirLaw k).prod L.seedLaw) i

/-- A guarantee for every positive finite benchmark, with the learner fixed before `P`. -/
def Guarantees (rho : ℝ) : Prop :=
  ∀ P : Instance n, P.HasPositiveFiniteMaximum → rho * P.expectedMaximum ≤ L.expectedReward P

end Learner

/-- One learner for each finite instance size, with the same hard budget independent of size. -/
def FeasibleBudget (eps : ℝ) (k : ℕ) : Prop :=
  ∃ learners : ∀ n : ℕ, Learner n k,
    ∀ n, (learners n).Guarantees (optimalCompetitiveRatio - eps)

/-- The least feasible hard budget `k_PS(ε)`, or infinity if there is none. -/
noncomputable def sampleComplexity (eps : ℝ) : ℕ∞ :=
  sInf {b : ℕ∞ | ∃ k : ℕ, FeasibleBudget eps k ∧ b = k}

end ProphetSecretary.Model
