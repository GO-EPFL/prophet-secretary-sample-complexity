import ProphetSecretary.Model.EmpiricalPolicy
import ProphetSecretary.Model.AllSamplesLearner

/-!
# A measurable empirical-policy learner

The scalar weights can be selected using the same full training array and an independent
auxiliary seed. The actual training protocol supplies every entry through its transcript,
and its per-marginal budget holds on every outcome. Freezing the training outcome gives
the canonical empirical optimizer proved by the finite Bellman theorem.
Paper correspondence: the random weight in `upstat:main` is chosen before online arrivals.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type*} [MeasurableSpace Seed]

/-- Both coefficients may use the entire training array and the same auxiliary seed. -/
noncomputable def empiricalSelectedPolicy (W C : Reservoir n k × Seed → ℝ) :
    Policy (Reservoir n k × Seed) n where
  decide p t i x h := (empiricalCanonicalPolicy (n := n) (k := k)).decide
    (p.1, (W p, C p)) t i x h

lemma empiricalSelectedPolicy_isMeasurable {W C : Reservoir n k × Seed → ℝ}
    (hW : Measurable W) (hC : Measurable C) :
    (empiricalSelectedPolicy W C).IsMeasurable := by
  have hpar : Measurable (fun p : Reservoir n k × Seed => (p.1, (W p, C p))) :=
    measurable_fst.prodMk (hW.prodMk hC)
  let T := (Reservoir n k × Seed) × (ℝ × (Fin n × (ℝ × History n)))
  have hm : Measurable (fun z : T => ((z.1.1, (W z.1, C z.1)), z.2)) :=
    (hpar.comp measurable_fst).prodMk measurable_snd
  have hcomp := (empiricalCanonicalPolicy_isMeasurable (n := n) (k := k)).comp hm
  change Measurable (fun z : T => (empiricalCanonicalPolicy (n := n) (k := k)).decide
    (z.1.1, (W z.1, C z.1)) z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
  convert hcomp using 1
  funext z
  rfl

/-- The sample-based rule is made into a law-independent, causal learner with hard
budget `k`. Its auxiliary law is fixed before the unknown instance. -/
noncomputable def Learner.empiricalWithSelectedWeights (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C) : Learner n k :=
  Learner.ofSamplePolicy Seed ν (empiricalSelectedPolicy W C) (empiricalSelectedPolicy_isMeasurable hW hC)

lemma Learner.empiricalWithSelectedWeights_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0 < W (y, r)) (hc : 0 ≤ C (y, r))
    (t : ℝ) (i : Fin n) (x : ℝ) (h : History n) :
    (Learner.empiricalWithSelectedWeights Seed ν W C hW hC).policy.decide (y, r) t i x h =
      ((totalEmpiricalInstance y).valuePolicy (totalEmpiricalInstance_integrable y) hw.le hc).rule.decide
        () t i x h := by
  change (Learner.ofSamplePolicy Seed ν (empiricalSelectedPolicy W C)
    (empiricalSelectedPolicy_isMeasurable hW hC)).policy.decide (y, r) t i x h = _
  rw [Learner.ofSamplePolicy_decide]
  exact empiricalCanonicalPolicy_decide y hw hc t i x h

/-- In particular, choosing a weight from the training data never changes the hard
sample-budget guarantee. There is no exceptional set in this statement. -/
lemma Learner.empiricalWithSelectedWeights_hardBudget (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (i : Fin n) :
    requests (trainingTranscript
      (Learner.empiricalWithSelectedWeights Seed ν W C hW hC).request r y) i ≤ k :=
  (Learner.empiricalWithSelectedWeights Seed ν W C hW hC).hard_budget r y i

/-- Freeze only the already observed training output and auxiliary seed. -/
noncomputable def Learner.frozenRule (L : Learner n k) (y : Reservoir n k) (r : L.Seed) : Policy Unit n where
  decide _ t i x h := L.policy.decide (y, r) t i x h

omit [NeZero k] in
lemma Learner.frozenRule_isMeasurable (L : Learner n k) (y : Reservoir n k) (r : L.Seed) :
    (L.frozenRule y r).IsMeasurable :=
  L.policy_isMeasurable.comp (measurable_const.prodMk measurable_snd)

noncomputable def Learner.frozenRandomizedPolicy (L : Learner n k) (y : Reservoir n k) (r : L.Seed) :
    RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := L.frozenRule y r
  measurable_rule := L.frozenRule_isMeasurable y r

/-- Exact conditional empirical optimality at every training outcome with valid
selected coefficients. Averaging under the true law is a separate statistical theorem. -/
theorem Learner.empiricalWithSelectedWeights_frozen_optimal (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0 < W (y, r)) (hc : 0 ≤ C (y, r)) :
    ((Learner.empiricalWithSelectedWeights Seed ν W C hW hC).frozenRandomizedPolicy y r).scalarObjective
      (totalEmpiricalInstance y) (W (y, r)) (C (y, r)) =
        optimalScalarValue (totalEmpiricalInstance y) (W (y, r)) (C (y, r)) := by
  let L := Learner.empiricalWithSelectedWeights Seed ν W C hW hC
  let Q := totalEmpiricalInstance y
  let π := Q.valuePolicy (totalEmpiricalInstance_integrable y) hw.le hc
  have hdec : (L.frozenRule y r).decide = π.rule.decide := by
    funext s t i x h
    cases s
    exact Learner.empiricalWithSelectedWeights_decide Seed ν W C hW hC y r hw hc t i x h
  have hRule : L.frozenRule y r = π.rule := congrArg Policy.mk hdec
  have hopt := Q.valuePolicy_optimal (totalEmpiricalInstance_integrable y) hw hc
  change (L.frozenRandomizedPolicy y r).scalarObjective Q (W (y, r)) (C (y, r)) = _
  change (∫ ω : World n Unit,
    W (y, r) * (L.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    C (y, r) * (L.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
      ∂Q.worldLaw (Measure.dirac ())) = _
  rw [hRule]
  exact hopt

end ProphetSecretary.Model
