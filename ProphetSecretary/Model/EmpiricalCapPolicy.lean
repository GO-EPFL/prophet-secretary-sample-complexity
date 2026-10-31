import ProphetSecretary.Model.EmpiricalLearner
import ProphetSecretary.Model.EmpiricalMomentsMeasurability
import ProphetSecretary.Model.PositiveValuePolicy
import ProphetSecretary.Model.MarkovAcceptance

/-!
# An empirical learner accepting caps and rejecting zero on every outcome

When the empirical expected maximum is at most 1/4, use its scalar threshold;
otherwise use the constant threshold 1. Reject zero at a zero threshold tie.
This is a genuine Markov threshold rule with a fixed zero tie convention.
Its threshold remains monotone under deletion of unseen identities, and its
sample protocol retains the hard per-distribution budget on every outcome.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def empiricalCapThreshold (y : Reservoir n k) (z : ℝ)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  if (totalEmpiricalInstance y).expectedMaximum ≤ 1/4 then empiricalValueThreshold y 1 z A t i else 1

lemma empiricalCapThreshold_monotone (y : Reservoir n k) (z t : ℝ) (i : Fin n)
    (A B : Finset (Fin n)) (hi : i ∈ A) (hAB : A ⊆ B) :
    empiricalCapThreshold y z A t i ≤ empiricalCapThreshold y z B t i := by
  unfold empiricalCapThreshold
  split_ifs
  · exact (totalEmpiricalInstance y).valueThreshold_monotone (totalEmpiricalInstance_integrable y)
      (positiveRewardWeight_pos 1) (le_max_left (0 : ℝ) z) () t i A B hi hAB
  · exact le_rfl

lemma empiricalCapThreshold_le_one (y : Reservoir n k) {z t : ℝ} (hz0 : 0 ≤ z)
    (hz : z ≤ 1/4) (ht : 0 ≤ t) (A : Finset (Fin n)) (i : Fin n) :
    empiricalCapThreshold y z A t i ≤ 1 := by
  unfold empiricalCapThreshold
  split_ifs with hM
  · rw [empiricalValueThreshold_eq y zero_lt_one hz0]
    have hθ := (totalEmpiricalInstance y).valueThreshold_le_initialValue
      (totalEmpiricalInstance_integrable y) zero_lt_one hz0 ht A i
    have hV := optimalScalarValue_le_benchmark (totalEmpiricalInstance y)
      (totalEmpiricalInstance_integrable y) zero_le_one hz0
    simp only [div_one,one_mul] at hθ hV
    linarith
  · exact le_rfl

lemma measurable_empiricalCapThreshold {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Reservoir n k} {z t : Ω → ℝ} {A : Ω → Finset (Fin n)} {i : Ω → Fin n}
    (hy : ∀ q j, Measurable fun ω => y ω q j) (hz : Measurable z) (ht : Measurable t)
    (hA : Measurable A) (hi : Measurable i) :
    Measurable (fun ω => empiricalCapThreshold (y ω) (z ω) (A ω) (t ω) (i ω)) := by
  exact Measurable.ite
    (measurableSet_le (measurable_totalEmpirical_expectedMaximum hy) measurable_const)
    (measurable_empiricalValueThreshold hy measurable_const hz ht hA hi) measurable_const

noncomputable def empiricalCapSelectedPolicy {Seed : Type*} (Z : Reservoir n k × Seed → ℝ) :
    Policy (Reservoir n k × Seed) n where
  decide p t i x H := decide (0 < x ∧ empiricalCapThreshold p.1 (Z p) (unseen H) t i ≤ x)

lemma empiricalCapSelectedPolicy_rejects_zero {Seed : Type*} (Z : Reservoir n k × Seed → ℝ)
    (p : Reservoir n k × Seed) (t : ℝ) (i : Fin n) (H : History n) :
    (empiricalCapSelectedPolicy Z).decide p t i 0 H = false := by
  simp [empiricalCapSelectedPolicy]

lemma empiricalCapSelectedPolicy_accepts_one {Seed : Type*} (Z : Reservoir n k × Seed → ℝ)
    (p : Reservoir n k × Seed) {t : ℝ} (ht : 0 ≤ t) (hz0 : 0 ≤ Z p) (hz : Z p ≤ 1/4)
    (i : Fin n) (H : History n) :
    (empiricalCapSelectedPolicy Z).decide p t i 1 H = true := by
  exact decide_eq_true ⟨zero_lt_one,empiricalCapThreshold_le_one p.1 hz0 hz ht (unseen H) i⟩

lemma empiricalCapSelectedPolicy_deletionMonotone {Seed : Type*} (Z : Reservoir n k × Seed → ℝ) :
    DeletionMonotoneAcceptance (fun p A t i x => decide (0 < x ∧ empiricalCapThreshold p.1 (Z p) A t i ≤ x)) := by
  intro p t _ht i x _hx A B hi hAB hacc
  have ha := of_decide_eq_true hacc
  exact decide_eq_true ⟨ha.1,(empiricalCapThreshold_monotone p.1 (Z p) t i A B hi hAB).trans ha.2⟩

lemma empiricalCapSelectedPolicy_isMeasurable {Seed : Type*} [MeasurableSpace Seed]
    {Z : Reservoir n k × Seed → ℝ} (hZ : Measurable Z) : (empiricalCapSelectedPolicy Z).IsMeasurable := by
  apply measurable_to_bool
  let T := (Reservoir n k × Seed) × (ℝ × (Fin n × (ℝ × History n)))
  change MeasurableSet {q : T | decide (0 < q.2.2.2.1 ∧
    empiricalCapThreshold q.1.1 (Z q.1) (unseen q.2.2.2.2) q.2.1 q.2.2.1 ≤ q.2.2.2.1) = true}
  simp only [decide_eq_true_eq]
  have hy (i : Fin n) (j : Fin k) : Measurable (fun q : T => q.1.1 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
  have ht : Measurable (fun q : T => q.2.1) := by fun_prop
  have hi : Measurable (fun q : T => q.2.2.1) := by fun_prop
  have hx : Measurable (fun q : T => q.2.2.2.1) := by fun_prop
  have hA : Measurable (fun q : T => unseen q.2.2.2.2) := measurable_unseen.comp (by fun_prop)
  exact (measurableSet_lt measurable_const hx).inter
    (measurableSet_le (measurable_empiricalCapThreshold hy (hZ.comp measurable_fst) ht hA hi) hx)

noncomputable def Learner.empiricalCapAcceptance (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z) : Learner n k :=
  Learner.ofSamplePolicy Seed ν (empiricalCapSelectedPolicy Z) (empiricalCapSelectedPolicy_isMeasurable hZ)

lemma Learner.empiricalCapAcceptance_hardBudget (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) (i : Fin n) :
    requests (trainingTranscript (Learner.empiricalCapAcceptance Seed ν Z hZ).request r y) i ≤ k :=
  (Learner.empiricalCapAcceptance Seed ν Z hZ).hard_budget r y i

lemma Learner.empiricalCapAcceptance_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.decide (y,r) t i x H =
      (empiricalCapSelectedPolicy Z).decide (y,r) t i x H :=
  Learner.ofSamplePolicy_decide Seed ν _ _ y r t i x H

lemma Learner.empiricalCapAcceptance_rejects_zero (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) (t : ℝ) (i : Fin n) (H : History n) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.decide (y,r) t i 0 H = false := by
  rw [Learner.empiricalCapAcceptance_decide]
  exact empiricalCapSelectedPolicy_rejects_zero Z (y,r) t i H

lemma Learner.empiricalCapAcceptance_accepts_one (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) {t : ℝ} (ht : 0 ≤ t)
    (hz0 : 0 ≤ Z (y,r)) (hz : Z (y,r) ≤ 1/4) (i : Fin n) (H : History n) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.decide (y,r) t i 1 H = true := by
  rw [Learner.empiricalCapAcceptance_decide]
  exact empiricalCapSelectedPolicy_accepts_one Z (y,r) ht hz0 hz i H

lemma empiricalCapThresholds_monotone {Seed : Type*} (Z : Reservoir n k × Seed → ℝ) :
    MonotoneThresholds (fun p A t i => empiricalCapThreshold p.1 (Z p) A t i) := by
  intro p t i A B hi hAB
  exact empiricalCapThreshold_monotone p.1 (Z p) t i A B hi hAB

end ProphetSecretary.Model
