import ProphetSecretary.Model.MixedEmpiricalPolicy
import ProphetSecretary.Model.EmpiricalLearner

/-!
# A causal empirical learner with declared known marginals

Both scalar weights may use all stored samples and an independent auxiliary seed.
The actual training protocol supplies those samples through its transcript and
has a hard budget on every outcome. Its policy depends on the supplied reference
instance only through the declared known marginal laws.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k] {Seed : Type*} [MeasurableSpace Seed]

/-- Both coefficients may use the entire training array and the same auxiliary seed. -/
noncomputable def mixedEmpiricalSelectedPolicy (D : Instance n) (known : Finset (Fin n)) (W C : Reservoir n k × Seed → ℝ) :
    Policy (Reservoir n k × Seed) n where
  decide p t i x h := (mixedEmpiricalCanonicalPolicy (n := n) (k := k) D known).decide
    (p.1, (W p, C p)) t i x h

lemma mixedEmpiricalSelectedPolicy_isMeasurable (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n)) {W C : Reservoir n k × Seed → ℝ}
    (hW : Measurable W) (hC : Measurable C) :
    (mixedEmpiricalSelectedPolicy D known W C).IsMeasurable := by
  have hpar : Measurable (fun p : Reservoir n k × Seed => (p.1, (W p, C p))) :=
    measurable_fst.prodMk (hW.prodMk hC)
  let T := (Reservoir n k × Seed) × (ℝ × (Fin n × (ℝ × History n)))
  have hm : Measurable (fun z : T => ((z.1.1, (W z.1, C z.1)), z.2)) :=
    (hpar.comp measurable_fst).prodMk measurable_snd
  have hcomp := (mixedEmpiricalCanonicalPolicy_isMeasurable (n := n) (k := k) D hD known).comp hm
  change Measurable (fun z : T => (mixedEmpiricalCanonicalPolicy (n := n) (k := k) D known).decide
    (z.1.1, (W z.1, C z.1)) z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
  convert hcomp using 1
  funext z
  rfl

/-- The sample-based rule is made into a law-independent, causal learner with hard
budget `k`. Its auxiliary law is fixed before the unknown instance. -/
noncomputable def Learner.mixedEmpiricalWithSelectedWeights (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n)) (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C) : Learner n k :=
  Learner.ofSamplePolicy Seed ν (mixedEmpiricalSelectedPolicy D known W C) (mixedEmpiricalSelectedPolicy_isMeasurable D hD known hW hC)

lemma Learner.mixedEmpiricalWithSelectedWeights_decide (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n)) (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0 < W (y, r)) (hc : 0 ≤ C (y, r))
    (t : ℝ) (i : Fin n) (x : ℝ) (h : History n) :
    (Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).policy.decide (y, r) t i x h =
      ((mixedEmpiricalInstance D known y).valuePolicy (mixedEmpiricalInstance_integrable D hD known y) hw.le hc).rule.decide
        () t i x h := by
  change (Learner.ofSamplePolicy Seed ν (mixedEmpiricalSelectedPolicy D known W C)
    (mixedEmpiricalSelectedPolicy_isMeasurable D hD known hW hC)).policy.decide (y, r) t i x h = _
  rw [Learner.ofSamplePolicy_decide]
  exact mixedEmpiricalCanonicalPolicy_decide D hD known y hw hc t i x h

/-- In particular, choosing a weight from the training data never changes the hard
sample-budget guarantee. There is no exceptional set in this statement. -/
lemma Learner.mixedEmpiricalWithSelectedWeights_hardBudget (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n)) (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (i : Fin n) :
    requests (trainingTranscript
      (Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).request r y) i ≤ k :=
  (Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).hard_budget r y i

omit [MeasurableSpace Seed] in
/-- The decision rule cannot use undeclared unknown marginal laws. -/
lemma mixedEmpiricalSelectedPolicy_congr_known {D E : Instance n} (known : Finset (Fin n))
    (hknown : ∀ i∈known, D.law i=E.law i) (W C : Reservoir n k × Seed → ℝ) :
    mixedEmpiricalSelectedPolicy D known W C = mixedEmpiricalSelectedPolicy E known W C := by
  apply congrArg Policy.mk
  funext p t i x h
  rw [mixedEmpiricalCanonicalPolicy_congr_known known hknown]

end ProphetSecretary.Model
