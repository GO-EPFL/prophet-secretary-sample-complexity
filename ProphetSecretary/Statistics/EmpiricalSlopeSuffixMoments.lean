import ProphetSecretary.Statistics.EmpiricalSlopeEnvelopeMeasurability

/-!
# Joint second and sixth moments of increment suffixes

Clock sorting is used only pointwise on the probability-one distinct-clock event.
The integrands are measurable finite maxima, so no measurable sorting choice is
needed to average the genuine sample martingale bounds.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma empiricalSlopeSuffix_integrable_pow (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ r)
      (P.trainingCoordinateLaw k) :=
  P.integrable_empiricalResidualSlopeSuffixEnvelope_pow hbound hz hzz (P.trainingCoordinateLaw k)
    (y := fun a => reservoirCoordinates.symm a) (u := fun _ => u)
    (fun i j => measurable_pi_apply (i, j)) (fun _ => measurable_const)
    (trainingCoordinates_unit_ae P hbound) r

lemma empiricalSlopeSuffix_joint_integrable_pow (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSlopeSuffixEnvelope P z z' v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  exact P.integrable_empiricalResidualSlopeSuffixEnvelope_pow (k := k) hbound hz hzz
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp measurable_snd)
    (hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)) r

lemma empiricalTrueSlopePremium_joint_integrable_pow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      empiricalTrueSlopePremiumSum P z z' v.2 v.1 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (Instance.clocksLaw n) := measurePreserving_snd
  exact integrable_empiricalTrueSlopePremiumSum_pow P (P.integrable_maximum_of_bounded hbound) hz hzz
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (a := Prod.fst) (u := Prod.snd) (fun q => (measurable_pi_apply q).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp measurable_snd)
    (hv.quasiMeasurePreserving.ae ((Instance.clocks_mem_unitInterval (n := n)).mono (fun u hu i => (hu i).1))) r

/-- Fixed-clock second moment of the paper's actual suffix envelope. -/
theorem empiricalSlopeSuffix_secondMoment (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (p : Equiv.Perm (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 2
      ∂P.trainingCoordinateLaw k) ≤
      (4 / (k : ℝ)) * (∫ a, empiricalTrueSlopePremiumSum P z z' u a
        ∂P.trainingCoordinateLaw k) := by
  apply (integral_mono (empiricalSlopeSuffix_integrable_pow P hbound hz hzz u 2)
    (empiricalSlopeReverseMaximum_integrable_pow P hbound p hz hzz u horder 2) ?_).trans
    (empiricalSlopeReverseMaximum_secondMoment P hbound p hz hzz u hu horder)
  intro a
  exact pow_le_pow_left₀ (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)
    (empiricalResidualSlopeSuffixEnvelope_le_reverseMaximum P p z z' u horder a) 2

/-- Fixed-clock sixth moment of the paper's actual suffix envelope. -/
theorem empiricalSlopeSuffix_sixthMoment (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (p : Equiv.Perm (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p) :
    (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 6
      ∂P.trainingCoordinateLaw k) ≤
      2000000000 * ((∫ a, empiricalTrueSlopePremiumSum P z z' u a ^ 3
        ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3 +
        (∫ a, empiricalTrueSlopePremiumSum P z z' u a
          ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5) := by
  apply (integral_mono (empiricalSlopeSuffix_integrable_pow P hbound hz hzz u 6)
    (empiricalSlopeReverseMaximum_integrable_pow P hbound p hz hzz u horder 6) ?_).trans
    (empiricalSlopeReverseMaximum_sixthMoment P hbound p hz hzz u hu horder)
  intro a
  exact pow_le_pow_left₀ (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)
    (empiricalResidualSlopeSuffixEnvelope_le_reverseMaximum P p z z' u horder a) 6

/-- The second part of `upstat:bdg`, averaged over both training and clocks. -/
theorem empiricalSlopeSuffix_secondMoment_clocks (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 2
      ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) ≤
      (4 / (k : ℝ)) * (∫ u, (∫ a, empiricalTrueSlopePremiumSum P z z' u a
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) := by
  have hXi : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 2 ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [Function.comp_def, Prod.swap] using (empiricalSlopeSuffix_joint_integrable_pow (k := k) P hbound hz hzz 2).swap.integral_prod_left
  have hU : Integrable (fun u => ∫ a, empiricalTrueSlopePremiumSum P z z' u a
      ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [pow_one, Function.comp_def, Prod.swap] using (empiricalTrueSlopePremium_joint_integrable_pow (k := k) P hbound hz hzz 1).swap.integral_prod_left
  have h := integral_mono_ae hXi (hU.const_mul (4 / (k : ℝ))) (by
    filter_upwards [Instance.clocks_pairwise_distinct (n := n), Instance.clocks_mem_unitInterval (n := n)] with u hd hu
    obtain ⟨p, hp⟩ := Instance.exists_arrivalOrder hd
    exact empiricalSlopeSuffix_secondMoment P hbound p hz hzz u (fun i => (hu i).1) hp)
  rw [integral_const_mul] at h
  exact h

/-- The sixth part of `upstat:bdg`, with a universal explicit constant. -/
theorem empiricalSlopeSuffix_sixthMoment_clocks (P : Instance n) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 6
      ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) ≤
      2000000000 * ((∫ u, (∫ a, empiricalTrueSlopePremiumSum P z z' u a ^ 3
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) / (k : ℝ) ^ 3 +
        (∫ u, (∫ a, empiricalTrueSlopePremiumSum P z z' u a
          ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) / (k : ℝ) ^ 5) := by
  have hXi : Integrable (fun u => ∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 6 ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [Function.comp_def, Prod.swap] using (empiricalSlopeSuffix_joint_integrable_pow (k := k) P hbound hz hzz 6).swap.integral_prod_left
  have hU3 : Integrable (fun u => ∫ a, empiricalTrueSlopePremiumSum P z z' u a ^ 3 ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [Function.comp_def, Prod.swap] using (empiricalTrueSlopePremium_joint_integrable_pow (k := k) P hbound hz hzz 3).swap.integral_prod_left
  have hU1 : Integrable (fun u => ∫ a, empiricalTrueSlopePremiumSum P z z' u a
      ∂P.trainingCoordinateLaw k) (Instance.clocksLaw n) := by
    simpa only [pow_one, Function.comp_def, Prod.swap] using (empiricalTrueSlopePremium_joint_integrable_pow (k := k) P hbound hz hzz 1).swap.integral_prod_left
  have h := integral_mono_ae hXi (((hU3.div_const ((k : ℝ) ^ 3)).add (hU1.div_const ((k : ℝ) ^ 5))).const_mul 2000000000) (by
    filter_upwards [Instance.clocks_pairwise_distinct (n := n), Instance.clocks_mem_unitInterval (n := n)] with u hd hu
    obtain ⟨p, hp⟩ := Instance.exists_arrivalOrder hd
    exact empiricalSlopeSuffix_sixthMoment P hbound p hz hzz u (fun i => (hu i).1) hp)
  change (∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 6 ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n) ≤
    ∫ u, 2000000000 * ((∫ a, empiricalTrueSlopePremiumSum P z z' u a ^ 3 ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3 +
      (∫ a, empiricalTrueSlopePremiumSum P z z' u a ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5) ∂Instance.clocksLaw n at h
  rw [integral_const_mul,
    integral_add (f := fun u => (∫ a, empiricalTrueSlopePremiumSum P z z' u a ^ 3 ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 3)
      (g := fun u => (∫ a, empiricalTrueSlopePremiumSum P z z' u a ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5)
      (hU3.div_const _) (hU1.div_const _), integral_div, integral_div] at h
  exact h

end ProphetSecretary.Model
