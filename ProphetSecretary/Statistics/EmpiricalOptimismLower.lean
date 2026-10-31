import ProphetSecretary.Statistics.EmpiricalCompleteResidual
import ProphetSecretary.Statistics.EmpiricalResidualBounds

/-!
# Nonnegative empirical optimism at a fixed scalar

Paper correspondence: the lower inequality in `upstat:optimism`. The true canonical
policy is fixed while training varies. Its clock-conditional reach weights therefore
multiply centered empirical residuals. The remaining design action loss is nonnegative.
The proof does not apply this cancellation to a training-selected scalar or policy.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

omit [NeZero k] in
private lemma trainingData_unit (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ i j, reservoirCoordinates.symm a i j ≤ 1 := by
  simp only [ae_all_iff]
  intro i j
  exact (measurePreserving_eval (fun q : Fin n × Fin k => P.law q.1) (i, j)).quasiMeasurePreserving.ae (hbound i)

noncomputable def RandomizedPolicy.empiricalClockResidual (π : RandomizedPolicy n) (P : Instance n)
    (z : ℝ) (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ i, π.rule.clockConditionalReach P π.seedLaw v.2 i *
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).transitionResidual P 1 z v.2 i

lemma RandomizedPolicy.measurable_empiricalClockResidual (π : RandomizedPolicy n) (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Measurable (π.empiricalClockResidual (k := k) P z) := by
  let Ω := (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))
  change Measurable (fun v : Ω => ∑ i : Fin n, π.rule.clockConditionalReach P π.seedLaw v.2 i *
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).transitionResidual P 1 z v.2 i)
  apply Finset.measurable_sum
  intro i _
  have hR : Measurable (fun v : Ω => π.rule.clockConditionalReach P π.seedLaw v.2 i) :=
    (π.rule.measurable_clockConditionalReach π.measurable_rule P π.seedLaw i).comp measurable_snd
  have hXi : Measurable (fun v : Ω => (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).transitionResidual P 1 z v.2 i) :=
    P.measurable_empiricalTransitionResidual (k := k) (P.integrable_maximum_of_bounded hbound)
      (y := fun v : Ω => reservoirCoordinates.symm v.1) (c := fun _ => z) (u := Prod.snd)
      (fun q j => (measurable_pi_apply (q, j)).comp measurable_fst) measurable_const (fun _ => hz)
      (fun q => (measurable_pi_apply q).comp measurable_snd) i
  exact hR.mul hXi

lemma RandomizedPolicy.integrable_empiricalClockResidual (π : RandomizedPolicy n) (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Integrable (π.empiricalClockResidual (k := k) P z)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  apply Integrable.of_bound (π.measurable_empiricalClockResidual P hbound hz).aestronglyMeasurable (n : ℝ)
  filter_upwards [hv.quasiMeasurePreserving.ae (trainingData_unit P hbound)] with v hvunit
  rw [Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (π.rule.clockConditionalReach_nonnegative P π.seedLaw v.2 i)]
      have hξ := (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).abs_transitionResidual_le_one_unitBounds P
        (totalEmpiricalInstance_bounded _ zero_le_one hvunit) hbound hz v.2 i
      exact (mul_le_mul (π.rule.clockConditionalReach_le_one P π.seedLaw v.2 i) hξ (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = n := by simp

/-- Training-independent competing policies have zero average reached residual at
fixed scalar weights. Both independent random experiments are actually integrated. -/
theorem RandomizedPolicy.integral_empiricalClockResidual_zero (π : RandomizedPolicy n) (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    (∫ a, (∫ u, π.empiricalClockResidual (k := k) P z (a, u) ∂Instance.clocksLaw n)
      ∂P.trainingCoordinateLaw k) = 0 := by
  rw [integral_integral_swap (f := fun (a : (Fin n × Fin k) → ℝ) (u : Fin n → ℝ) =>
    π.empiricalClockResidual (k := k) P z (a, u)) (π.integrable_empiricalClockResidual (k := k) P hbound hz)]
  apply integral_eq_zero_of_ae
  filter_upwards [Instance.clocks_pairwise_distinct (n := n)] with u hu
  obtain ⟨p, hp⟩ := Instance.exists_arrivalOrder hu
  exact integral_weighted_empirical_transitionResidual_zero P hbound p hz u hp
    (π.rule.clockConditionalReach P π.seedLaw u)

lemma integrable_empiricalScalarValue_unit (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Integrable (fun a : (Fin n × Fin k) → ℝ => optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z)
      (P.trainingCoordinateLaw k) := by
  have hm : Measurable (fun a : (Fin n × Fin k) → ℝ => optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z) :=
    measurable_optimalScalarValue_totalEmpirical (y := fun a => reservoirCoordinates.symm a)
      (w := fun _ => 1) (c := fun _ => z) (fun i j => measurable_pi_apply (i, j))
      measurable_const measurable_const (fun _ => by norm_num) (fun _ => hz)
  apply Integrable.of_bound hm.aestronglyMeasurable (1 + z)
  filter_upwards [trainingData_unit (k := k) P hbound] with a ha
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm a)
  have h0 := optimalScalarValue_nonnegative Q hQ zero_le_one hz
  have h1 := optimalScalarValue_le_benchmark Q hQ zero_le_one hz
  have hM : Q.expectedMaximum ≤ 1 := Q.expectedMaximum_le_of_bounded zero_le_one (totalEmpiricalInstance_bounded _ zero_le_one ha)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith

/-- The fixed-weight nonnegative bias statement, with the full general-policy
optimal values and the genuine iid training law. The upper statistical rate is separate. -/
theorem empiricalScalarValue_expected_optimism_nonnegative (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ (∫ a : (Fin n × Fin k) → ℝ,
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k) -
      optimalScalarValue P 1 z := by
  have hP := P.integrable_maximum_of_bounded hbound
  let π := P.valuePolicy hP zero_le_one hz
  have hW := π.integrable_empiricalClockResidual (k := k) P hbound hz
  have hWI := hW.integral_prod_left
  have hVI := integrable_empiricalScalarValue_unit (k := k) P hbound hz
  have hineq : (∫ a, (∫ u, π.empiricalClockResidual P z (a, u) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) ≤
      ∫ a, optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z - optimalScalarValue P 1 z
        ∂P.trainingCoordinateLaw k := by
    apply integral_mono hWI (hVI.sub (integrable_const _))
    intro a
    let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
    have h := π.bellman_residualIdentity_clocks Q P (totalEmpiricalInstance_integrable _) hP (by norm_num : (0 : ℝ) < 1) hz
    have hopt : π.scalarObjective P 1 z = optimalScalarValue P 1 z := P.valuePolicy_optimal hP (by norm_num : (0 : ℝ) < 1) hz
    rw [hopt] at h
    have hloss := π.expectedReachedDesignActionLoss_nonnegative Q P 1 z
    change (∫ u, ∑ i : Fin n, π.rule.clockConditionalReach P π.seedLaw u i * Q.transitionResidual P 1 z u i
      ∂Instance.clocksLaw n) ≤ optimalScalarValue Q 1 z - optimalScalarValue P 1 z
    linarith
  rw [π.integral_empiricalClockResidual_zero P hbound hz,
    integral_sub hVI (integrable_const _), integral_const, probReal_univ, one_smul] at hineq
  exact hineq

end ProphetSecretary.Model
