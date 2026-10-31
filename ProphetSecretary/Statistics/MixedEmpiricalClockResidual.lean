import ProphetSecretary.Statistics.MixedEmpiricalCompleteResidual
import ProphetSecretary.Statistics.MixedEmpiricalResidualBounds
import ProphetSecretary.Statistics.MixedEmpiricalSuffixMoments

/-!
# Fixed-policy mixed residual means

Clock-conditional reach weights of a policy fixed before training may multiply
the mixed signed residuals. The actual row-centering theorem then gives zero
mean. Known marginals have zero residuals, and no sample-selected scalar is
substituted into this fixed-weight identity.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def RandomizedPolicy.mixedClockResidual (π : RandomizedPolicy n) (P : Instance n) (known : Finset (Fin n))
    (z : ℝ) (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ i, π.rule.clockConditionalReach P π.seedLaw v.2 i *
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).transitionResidual P 1 z v.2 i

lemma RandomizedPolicy.measurable_mixedClockResidual (π : RandomizedPolicy n) (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Measurable (π.mixedClockResidual (k := k) P known z) := by
  let Ω := (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))
  change Measurable (fun v : Ω => ∑ i : Fin n, π.rule.clockConditionalReach P π.seedLaw v.2 i *
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).transitionResidual P 1 z v.2 i)
  apply Finset.measurable_sum
  intro i _
  have hR : Measurable (fun v : Ω => π.rule.clockConditionalReach P π.seedLaw v.2 i) :=
    (π.rule.measurable_clockConditionalReach π.measurable_rule P π.seedLaw i).comp measurable_snd
  have hXi : Measurable (fun v : Ω => (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).transitionResidual P 1 z v.2 i) :=
    P.measurable_mixedTransitionResidual (k := k) (P.integrable_maximum_of_bounded hbound) known
      (y := fun v : Ω => reservoirCoordinates.symm v.1) (c := fun _ => z) (u := Prod.snd)
      (fun q j => (measurable_pi_apply (q, j)).comp measurable_fst) measurable_const (fun _ => hz)
      (fun q => (measurable_pi_apply q).comp measurable_snd) i
  exact hR.mul hXi

lemma RandomizedPolicy.integrable_mixedClockResidual (π : RandomizedPolicy n) (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Integrable (π.mixedClockResidual (k := k) P known z)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  apply Integrable.of_bound (π.measurable_mixedClockResidual P known hbound hz).aestronglyMeasurable (n : ℝ)
  filter_upwards [hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)] with v hvunit
  rw [Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (π.rule.clockConditionalReach_nonnegative P π.seedLaw v.2 i)]
      have hξ := (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).abs_transitionResidual_le_one_unitBounds P
        (mixedEmpiricalInstance_bounded P known _ zero_le_one hbound hvunit) hbound hz v.2 i
      exact (mul_le_mul (π.rule.clockConditionalReach_le_one P π.seedLaw v.2 i) hξ (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = n := by simp

/-- Training-independent competing policies have zero average reached residual at
fixed scalar weights. Both independent random experiments are actually integrated. -/
theorem RandomizedPolicy.integral_mixedClockResidual_zero (π : RandomizedPolicy n) (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    (∫ a, (∫ u, π.mixedClockResidual (k := k) P known z (a, u) ∂Instance.clocksLaw n)
      ∂P.trainingCoordinateLaw k) = 0 := by
  rw [integral_integral_swap (f := fun (a : (Fin n × Fin k) → ℝ) (u : Fin n → ℝ) =>
    π.mixedClockResidual (k := k) P known z (a, u)) (π.integrable_mixedClockResidual (k := k) P known hbound hz)]
  apply integral_eq_zero_of_ae
  filter_upwards [Instance.clocks_pairwise_distinct (n := n)] with u hu
  obtain ⟨p, hp⟩ := Instance.exists_arrivalOrder hu
  exact integral_weighted_mixed_transitionResidual_zero P known hbound p hz u hp
    (π.rule.clockConditionalReach P π.seedLaw u)

end ProphetSecretary.Model
