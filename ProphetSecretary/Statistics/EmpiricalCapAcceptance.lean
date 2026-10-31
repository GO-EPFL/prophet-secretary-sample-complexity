import ProphetSecretary.Model.EmpiricalCapAgreement
import ProphetSecretary.Model.LearnerConditioning
import ProphetSecretary.Statistics.EmpiricalMaximumTail

/-!
# Expected cost of accepting empirical caps and rejecting zero

Paper correspondence: `lem:empirical-cap-acceptance`. The selected scalar may
use the same training array and an independent auxiliary seed. Agreement on
the good training event is proved under the actual true online law. On the
bad event, a uniform payoff bound combines with the explicit empirical-
maximum probability estimate; no selected-weight independence is assumed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

omit [NeZero k] in
private lemma frozen_scalar_mem_interval (L : Learner n k) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (y : Reservoir n k) (r : L.Seed)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1/4) :
    (L.frozenRandomizedPolicy y r).scalarObjective P 1 z ∈ Icc (0 : ℝ) (5/4) := by
  let π := L.frozenRandomizedPolicy y r
  have hP := P.integrable_maximum_of_bounded hcap
  have h0 : 0 ≤ π.scalarObjective P 1 z := by
    rw [π.scalarObjective_eq P hP]
    exact add_nonneg (mul_nonneg zero_le_one (π.expectedReward_nonnegative P))
      (mul_nonneg hz0 (π.expectedDuration_nonnegative P))
  have hV := (scalarObjective_le_optimal π P hP zero_le_one hz0).trans
    (optimalScalarValue_le_benchmark P hP zero_le_one hz0)
  have hM := P.expectedMaximum_le_of_bounded zero_le_one hcap
  refine ⟨h0,?_⟩
  simp only [one_mul] at hV
  linarith

/-- The expected payoff loss relative to the original empirical optimizer,
with an explicit bound and the same selected scalar on both sides. -/
theorem Learner.empiricalCapAcceptance_expected_loss (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    {lo : ℝ} (hlo : 0 < lo) (hZlo : ∀ p, lo ≤ Z p) (hZhi : ∀ p, Z p ≤ 1/4)
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (hM : P.expectedMaximum ≤ 1/80) :
    let L := Learner.empiricalCapAcceptance Seed ν Z hZ
    let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
    (∫ p, (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)-
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ∂(P.reservoirLaw k).prod ν) ≤
      (5/4 : ℝ)*P.expectedMaximum/((k : ℝ)*((1/4 : ℝ)-P.expectedMaximum)^2) := by
  let L := Learner.empiricalCapAcceptance Seed ν Z hZ
  let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
  let D := (P.reservoirLaw k).prod ν
  let E : Set (Reservoir n k × Seed) := {p | (1/4 : ℝ) < (totalEmpiricalInstance p.1).expectedMaximum}
  let loss := fun p : Reservoir n k × Seed =>
    (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)-
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  have hzpos (p : Reservoir n k × Seed) : 0 < Z p := hlo.trans_le (hZlo p)
  have hP := P.integrable_maximum_of_bounded hcap
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_totalEmpirical_expectedMaximum (fun i j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)))
  have hK := K.integrable_selectedRegret P hP hZ (fun p => (hzpos p).le) (Eventually.of_forall hZhi)
  have hL := L.integrable_selectedRegret P hP hZ (fun p => (hzpos p).le) (Eventually.of_forall hZhi)
  have hLoss : Integrable loss D := by
    apply (hL.sub hK).congr
    exact Eventually.of_forall fun p => by dsimp only [loss,Pi.sub_apply]; ring
  have hpoint (p : Reservoir n k × Seed) : loss p ≤ E.indicator (fun _ => (5/4 : ℝ)) p := by
    by_cases hp : p ∈ E
    · rw [Set.indicator_of_mem hp]
      have hKo := frozen_scalar_mem_interval K P hcap p.1 p.2 (hzpos p).le (hZhi p)
      have hLo := frozen_scalar_mem_interval L P hcap p.1 p.2 (hzpos p).le (hZhi p)
      exact (sub_le_self _ hLo.1).trans hKo.2
    · rw [Set.indicator_of_notMem hp]
      have hgood : (totalEmpiricalInstance p.1).expectedMaximum ≤ 1/4 := not_lt.mp hp
      have he := Learner.empiricalCapAcceptance_good_scalarObjective Seed ν Z hZ p.1 p.2 hgood (hzpos p) P
      change (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)-
        (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ≤ 0
      exact le_of_eq (sub_eq_zero.mpr he.symm)
  have hInt := integral_mono hLoss ((integrable_const (5/4 : ℝ)).indicator hE) hpoint
  rw [integral_indicator_const (5/4 : ℝ) hE,smul_eq_mul] at hInt
  have hEb : MeasurableSet {y : Reservoir n k | (1/4 : ℝ) < (totalEmpiricalInstance y).expectedMaximum} :=
    measurableSet_lt measurable_const (measurable_totalEmpirical_expectedMaximum (fun i j =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)))
  have hp := (measurePreserving_fst (μ := P.reservoirLaw k) (ν := ν)).measure_preimage hEb.nullMeasurableSet
  have hEq : D.real E = (P.reservoirLaw k).real {y | (1/4 : ℝ) < (totalEmpiricalInstance y).expectedMaximum} :=
    congrArg ENNReal.toReal hp
  have ha : P.expectedMaximum < (1/4 : ℝ) := by linarith
  have hProb := P.reservoir_empiricalExpectedMaximum_upper_tail (k := k) hcap ha
  change (∫ p, loss p ∂D) ≤ _
  calc
    _ ≤ D.real E*(5/4 : ℝ) := hInt
    _ = (5/4 : ℝ)*(P.reservoirLaw k).real {y | (1/4 : ℝ) < (totalEmpiricalInstance y).expectedMaximum} := by rw [hEq,mul_comm]
    _ ≤ (5/4 : ℝ)*(P.expectedMaximum/((k : ℝ)*((1/4 : ℝ)-P.expectedMaximum)^2)) :=
      mul_le_mul_of_nonneg_left hProb (by norm_num)
    _ = _ := by ring

/-- Explicit uniform O(1/k) modification cost, independent of instance size
and of how the valid scalar was selected from the training samples. -/
theorem Learner.empiricalCapAcceptance_expected_loss_le_const (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    {lo : ℝ} (hlo : 0 < lo) (hZlo : ∀ p, lo ≤ Z p) (hZhi : ∀ p, Z p ≤ 1/4)
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (hM : P.expectedMaximum ≤ 1/80) :
    let L := Learner.empiricalCapAcceptance Seed ν Z hZ
    let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
    (∫ p, (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)-
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ∂(P.reservoirLaw k).prod ν) ≤
      (100/361 : ℝ)/(k : ℝ) := by
  apply (Learner.empiricalCapAcceptance_expected_loss Seed ν Z hZ hlo hZlo hZhi P hcap hM).trans
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have ha : P.expectedMaximum < (1/4 : ℝ) := by linarith
  have hg : 0 < (1/4 : ℝ)-P.expectedMaximum := sub_pos.mpr ha
  apply (div_le_iff₀ (mul_pos hk (sq_pos_of_pos hg))).mpr
  have he : (100/361 : ℝ)/(k : ℝ)*((k : ℝ)*((1/4 : ℝ)-P.expectedMaximum)^2) =
      (100/361 : ℝ)*((1/4 : ℝ)-P.expectedMaximum)^2 := by field_simp
  rw [he]
  have h0 := P.expectedMaximum_nonnegative
  nlinarith [sq_nonneg P.expectedMaximum]

end ProphetSecretary.Model
