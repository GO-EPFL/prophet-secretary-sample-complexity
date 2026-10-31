import ProphetSecretary.Statistics.EmpiricalSuffixBridge
import ProphetSecretary.Statistics.EmpiricalResidualBounds

/-!
# Empirical residual suffix maximal moments

Paper correspondence: `upstat:bdg`. The deterministic suffix/block bridge transfers the
actual reverse-sample maximal inequalities. The estimates are then integrated against
the independent uniform clock law, using joint measurability and explicit integrability.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

omit [NeZero k] in
lemma trainingCoordinates_unit_ae (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ i j, reservoirCoordinates.symm a i j ≤ 1 := by
  simp only [ae_all_iff]
  intro i j
  exact (measurePreserving_eval (fun q : Fin n × Fin k => P.law q.1) (i, j)).quasiMeasurePreserving.ae (hbound i)

lemma empiricalSuffix_integrable_pow (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ r)
      (P.trainingCoordinateLaw k) :=
  P.integrable_empiricalResidualSuffixEnvelope_pow hbound (P.trainingCoordinateLaw k)
    (y := fun a => reservoirCoordinates.symm a) (c := fun _ => z) (u := fun _ => u)
    (fun i j => measurable_pi_apply (i, j)) measurable_const (fun _ => hz) (fun _ => measurable_const)
    (trainingCoordinates_unit_ae P hbound) r

lemma empiricalSuffix_joint_integrable_pow (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  exact P.integrable_empiricalResidualSuffixEnvelope_pow (k := k) hbound ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1) (c := fun _ => z) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hz)
    (fun i => (measurable_pi_apply i).comp measurable_snd)
    (hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)) r

lemma empiricalTruePremium_joint_integrable_pow (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) :=
  P.integrable_empiricalPremiumUnder_pow (k := k) (P.integrable_maximum_of_bounded hbound) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1) (c := fun _ => z) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hz)
    (fun i => (measurable_pi_apply i).comp measurable_snd) r

/-- Fixed-clock second moment of the paper's actual suffix envelope. -/
theorem empiricalSuffix_secondMoment (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (p : Equiv.Perm (Fin n)) {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 2
      ∂P.trainingCoordinateLaw k) ≤
      (4 / (k : ℝ)) * (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) := by
  apply (integral_mono (empiricalSuffix_integrable_pow P hbound hz u 2)
    (empiricalReverseMaximum_integrable_pow P hbound p hz u horder 2) ?_).trans
    (empiricalReverseMaximum_secondMoment P hbound p hz u horder)
  intro a
  exact pow_le_pow_left₀ (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)
    (empiricalResidualSuffixEnvelope_le_reverseMaximum P p z u horder a) 2

/-- Fixed-clock sixth moment of the paper's actual suffix envelope. -/
theorem empiricalSuffix_sixthMoment (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (p : Equiv.Perm (Fin n)) {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 6
      ∂P.trainingCoordinateLaw k) ≤
      2000000000 * ((∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3
        ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3 +
        (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
          ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5) := by
  apply (integral_mono (empiricalSuffix_integrable_pow P hbound hz u 6)
    (empiricalReverseMaximum_integrable_pow P hbound p hz u horder 6) ?_).trans
    (empiricalReverseMaximum_sixthMoment P hbound p hz u horder)
  intro a
  exact pow_le_pow_left₀ (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)
    (empiricalResidualSuffixEnvelope_le_reverseMaximum P p z u horder a) 6

/-- The second part of `upstat:bdg`, averaged over both training and clocks. -/
theorem empiricalSuffix_secondMoment_clocks (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 2
      ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) ≤
      (4 / (k : ℝ)) * (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) := by
  have hXi : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 2 ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [Function.comp_def, Prod.swap] using (empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 2).swap.integral_prod_left
  have hU : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
      ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [pow_one, Function.comp_def, Prod.swap] using (empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 1).swap.integral_prod_left
  have h := integral_mono_ae hXi (hU.const_mul (4 / (k : ℝ))) (by
    filter_upwards [Instance.clocks_pairwise_distinct (n := n)] with u hu
    obtain ⟨p, hp⟩ := Instance.exists_arrivalOrder hu
    exact empiricalSuffix_secondMoment P hbound p hz u hp)
  rw [integral_const_mul] at h
  exact h

/-- The sixth part of `upstat:bdg`, with a universal explicit constant. -/
theorem empiricalSuffix_sixthMoment_clocks (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 6
      ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) ≤
      2000000000 * ((∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) / (k : ℝ) ^ 3 +
        (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
          ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) / (k : ℝ) ^ 5) := by
  have hXi : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 6 ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [Function.comp_def, Prod.swap] using (empiricalSuffix_joint_integrable_pow (k := k) P hbound hz 6).swap.integral_prod_left
  have hU3 : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3 ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [Function.comp_def, Prod.swap] using (empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 3).swap.integral_prod_left
  have hU1 : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
      ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [pow_one, Function.comp_def, Prod.swap] using (empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 1).swap.integral_prod_left
  have h := integral_mono_ae hXi (((hU3.div_const ((k : ℝ) ^ 3)).add (hU1.div_const ((k : ℝ) ^ 5))).const_mul 2000000000) (by
    filter_upwards [Instance.clocks_pairwise_distinct (n := n)] with u hu
    obtain ⟨p, hp⟩ := Instance.exists_arrivalOrder hu
    exact empiricalSuffix_sixthMoment P hbound p hz u hp)
  change (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 6 ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) ≤
    ∫ u, 2000000000 * ((∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3 ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3 +
      (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5) ∂Instance.clocksLaw n at h
  rw [integral_const_mul,
    integral_add (f := fun u => (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3 ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3)
      (g := fun u => (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5)
      (hU3.div_const _) (hU1.div_const _), integral_div, integral_div] at h
  exact h

end ProphetSecretary.Model
