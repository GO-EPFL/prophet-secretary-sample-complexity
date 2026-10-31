import ProphetSecretary.Statistics.EmpiricalSuffixMoments
import ProphetSecretary.Statistics.EmpiricalDesignPremium
import ProphetSecretary.Statistics.PremiumKac

/-!
# Joint empirical moments

All moment definitions use the independent product of the genuine training-coordinate
law and the independent uniform-clock law. The full statistical inequalities retain
explicit constants. Empirical scalar values are integrated over training alone.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.empiricalSuffixMoment (P : Instance n) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.empiricalTruePremiumMoment (P : Instance n) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.empiricalDesignPremiumMoment (P : Instance n) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremium 1 z v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.empiricalScalarValueMoment (P : Instance n) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ a : (Fin n × Fin k) → ℝ, optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ^ r
    ∂P.trainingCoordinateLaw k

variable {k : ℕ} [NeZero k]

lemma Instance.empiricalSuffixMoment_nonnegative (P : Instance n) (z : ℝ) (r : ℕ) :
    0 ≤ P.empiricalSuffixMoment k z r := integral_nonneg (fun _ =>
      pow_nonneg (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _) r)

lemma Instance.empiricalTruePremiumMoment_nonnegative (P : Instance n) (z : ℝ) (r : ℕ) :
    0 ≤ P.empiricalTruePremiumMoment k z r := integral_nonneg (fun v =>
      pow_nonneg ((totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder_nonnegative P 1 z v.2) r)

lemma empiricalDesignPremium_joint_integrable_pow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremium 1 z v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  exact integrable_empiricalUnstoppedPremium_pow (k := k) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
    (c := fun _ => z) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hz)
    (fun i => (measurable_pi_apply i).comp measurable_snd)
    (hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)) r

lemma empiricalScalarValue_integrable_pow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ^ r) (P.trainingCoordinateLaw k) :=
  integrable_empiricalScalarValue_pow_unit (k := k) (P.trainingCoordinateLaw k)
    (y := fun a => reservoirCoordinates.symm a) (c := fun _ => z)
    (fun i j => measurable_pi_apply (i, j)) measurable_const (fun _ => hz)
    (Filter.Eventually.of_forall (fun _ => le_refl z)) (trainingCoordinates_unit_ae P hbound) r

/-- Actual joint version of `upstat:bdg` for the second moment. -/
theorem Instance.empiricalSuffixMoment_two_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalSuffixMoment k z 2 ≤ (4 / (k : ℝ)) * P.empiricalTruePremiumMoment k z 1 := by
  have h := empiricalSuffix_secondMoment_clocks (k := k) P hbound hz
  have hXi : P.empiricalSuffixMoment k z 2 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 2
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (empiricalSuffix_joint_integrable_pow P hbound hz 2)
  have hU : P.empiricalTruePremiumMoment k z 1 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.empiricalTruePremiumMoment, pow_one] using integral_prod_symm _ (empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 1)
  rw [← hXi, ← hU] at h
  exact h

/-- Actual joint version of `upstat:bdg` for the sixth moment. -/
theorem Instance.empiricalSuffixMoment_six_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalSuffixMoment k z 6 ≤ 2000000000 *
      (P.empiricalTruePremiumMoment k z 3 / (k : ℝ) ^ 3 + P.empiricalTruePremiumMoment k z 1 / (k : ℝ) ^ 5) := by
  have h := empiricalSuffix_sixthMoment_clocks (k := k) P hbound hz
  have hXi : P.empiricalSuffixMoment k z 6 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 6
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (empiricalSuffix_joint_integrable_pow P hbound hz 6)
  have hU3 : P.empiricalTruePremiumMoment k z 3 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (empiricalTruePremium_joint_integrable_pow P hbound hz 3)
  have hU1 : P.empiricalTruePremiumMoment k z 1 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.empiricalTruePremiumMoment, pow_one] using integral_prod_symm _ (empiricalTruePremium_joint_integrable_pow (k := k) P hbound hz 1)
  rw [← hXi, ← hU3, ← hU1] at h
  exact h

/-- Actual empirical-design Kac bound, then averaged over training. -/
theorem Instance.empiricalDesignPremiumMoment_three_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.empiricalDesignPremiumMoment k z 3 ≤ 13 * P.empiricalScalarValueMoment k z 3 := by
  have hI := empiricalDesignPremium_joint_integrable_pow (k := k) P hbound hz 3
  have hV := empiricalScalarValue_integrable_pow (k := k) P hbound hz 3
  rw [Instance.empiricalDesignPremiumMoment, integral_prod _ hI]
  have h := integral_mono hI.integral_prod_left (hV.const_mul 13) (fun a =>
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremium_kac
      (totalEmpiricalInstance_integrable _) (by norm_num : (0 : ℝ) < 1) hz |>.2)
  rw [integral_const_mul] at h
  exact h

end ProphetSecretary.Model
