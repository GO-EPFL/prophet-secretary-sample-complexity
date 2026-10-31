import ProphetSecretary.Model.EmpiricalCapPolicy
import ProphetSecretary.Model.ExecutionAgreement

/-!
# Agreement of the cap modification off its bad training event

On empirical expected maximum at most 1/4, the modification differs from the
usual empirical canonical rule only in zero-threshold tie choices. With a
positive selected duration weight, every preterminal threshold is positive.
The actual two frozen executions therefore agree under any independent
online law almost surely, including their reward and stopping time.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma empiricalCapSelectedPolicy_good_decide {Seed : Type*} (Z : Reservoir n k × Seed → ℝ)
    (p : Reservoir n k × Seed) (hgood : (totalEmpiricalInstance p.1).expectedMaximum ≤ 1/4)
    (hz : 0 < Z p) {t : ℝ} (ht : t < 1) (i : Fin n) (x : ℝ) (H : History n) :
    (empiricalCapSelectedPolicy Z).decide p t i x H =
      (empiricalSelectedPolicy (fun _ => 1) Z).decide p t i x H := by
  change decide (0 < x ∧ empiricalCapThreshold p.1 (Z p) (unseen H) t i ≤ x) =
    decide (empiricalValueThreshold p.1 1 (Z p) (unseen H) t i ≤ x)
  rw [empiricalCapThreshold,if_pos hgood]
  have hpos : 0 < empiricalValueThreshold p.1 1 (Z p) (unseen H) t i := by
    rw [empiricalValueThreshold_eq p.1 zero_lt_one hz.le]
    exact (totalEmpiricalInstance p.1).valueThreshold_positive
      (totalEmpiricalInstance_integrable p.1) zero_lt_one hz ht (unseen H) i
  by_cases ha : empiricalValueThreshold p.1 1 (Z p) (unseen H) t i ≤ x
  · simp [ha,hpos.trans_le ha]
  · simp [ha]

lemma empiricalCapSelectedPolicy_bad_decide {Seed : Type*} (Z : Reservoir n k × Seed → ℝ)
    (p : Reservoir n k × Seed) (hbad : (1/4 : ℝ) < (totalEmpiricalInstance p.1).expectedMaximum)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (empiricalCapSelectedPolicy Z).decide p t i x H = decide (1 ≤ x) := by
  change decide (0 < x ∧ empiricalCapThreshold p.1 (Z p) (unseen H) t i ≤ x) = _
  rw [empiricalCapThreshold,if_neg (not_le.mpr hbad)]
  by_cases ha : 1 ≤ x
  · simp [ha,zero_lt_one.trans_le ha]
  · simp [ha]

lemma Learner.empiricalCapAcceptance_good_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) (hgood : (totalEmpiricalInstance y).expectedMaximum ≤ 1/4)
    (hz : 0 < Z (y,r)) {t : ℝ} (ht : t < 1) (i : Fin n) (x : ℝ) (H : History n) :
    (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.decide (y,r) t i x H =
      (Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).policy.decide (y,r) t i x H := by
  change (Learner.empiricalCapAcceptance Seed ν Z hZ).policy.decide (y,r) t i x H =
    (Learner.ofSamplePolicy Seed ν (empiricalSelectedPolicy (fun _ => 1) Z)
      (empiricalSelectedPolicy_isMeasurable measurable_const hZ)).policy.decide (y,r) t i x H
  rw [Learner.empiricalCapAcceptance_decide,Learner.ofSamplePolicy_decide]
  exact empiricalCapSelectedPolicy_good_decide Z (y,r) hgood hz ht i x H

/-- Conditional true-law payoff equality, even though the positive empirical
design law may differ from the evaluation instance. -/
theorem Learner.empiricalCapAcceptance_good_scalarObjective (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n k) (r : Seed) (hgood : (totalEmpiricalInstance y).expectedMaximum ≤ 1/4)
    (hz : 0 < Z (y,r)) (P : Instance n) :
    ((Learner.empiricalCapAcceptance Seed ν Z hZ).frozenRandomizedPolicy y r).scalarObjective P 1 (Z (y,r)) =
      ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy y r).scalarObjective P 1 (Z (y,r)) := by
  let L := Learner.empiricalCapAcceptance Seed ν Z hZ
  let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
  have hne : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ i, ω.2.1 i ≠ 1 :=
    ae_all_iff.mpr fun i => (P.world_clock_measurePreserving (Measure.dirac ()) i).quasiMeasurePreserving.ae
      (Instance.uniformClock.ae_ne 1)
  have htime : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ i, ω.2.1 i < 1 := by
    filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ()),hne] with ω hω hn
    exact fun i => lt_of_le_of_ne (hω i).2 (hn i)
  apply integral_congr_ae
  filter_upwards [htime] with ω hω
  have ha (i : Fin n) : (L.frozenRule y r).action ω.2.2 Finset.univ ω.1 ω.2.1 i =
      (K.frozenRule y r).action ω.2.2 Finset.univ ω.1 ω.2.1 i := by
    exact Learner.empiricalCapAcceptance_good_decide Seed ν Z hZ y r hgood hz (hω i) i (ω.1 i)
      (history Finset.univ ω.1 ω.2.1 (ω.2.1 i))
  have he := (L.frozenRule y r).outcomes_eq_of_actions_eq (K.frozenRule y r) ω.2.2 ω.2.2 Finset.univ ω.1 ω.2.1 ha
  change 1*(L.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    Z (y,r)*(L.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 =
      1*(K.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    Z (y,r)*(K.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  rw [he.1,he.2]

end ProphetSecretary.Model
