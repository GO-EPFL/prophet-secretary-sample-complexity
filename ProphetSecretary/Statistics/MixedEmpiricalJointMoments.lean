import ProphetSecretary.Statistics.MixedEmpiricalSuffixMoments
import ProphetSecretary.Statistics.MixedEmpiricalDesignPremium
import ProphetSecretary.Statistics.PremiumKac

/-!
# Joint mixed empirical moments

All moments use the genuine independent training-coordinate and uniform-clock
product law. Known marginals are exact in the design instance. The constructed
reverse-martingale estimates and generic design-law Kac identities retain the
same explicit constants as for fully empirical instances.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.mixedSuffixMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.mixedTruePremiumMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 z v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.mixedDesignPremiumMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremium 1 z v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.mixedScalarValueMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z : ℝ) (r : ℕ) : ℝ :=
  ∫ a : (Fin n × Fin k) → ℝ, optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ^ r
    ∂P.trainingCoordinateLaw k

variable {k : ℕ} [NeZero k]

lemma Instance.mixedSuffixMoment_nonnegative (P : Instance n) (known : Finset (Fin n)) (z : ℝ) (r : ℕ) :
    0 ≤ P.mixedSuffixMoment known k z r := integral_nonneg (fun _ =>
      pow_nonneg (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _) r)

lemma Instance.mixedTruePremiumMoment_nonnegative (P : Instance n) (known : Finset (Fin n)) (z : ℝ) (r : ℕ) :
    0 ≤ P.mixedTruePremiumMoment known k z r := integral_nonneg (fun v =>
      pow_nonneg ((mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder_nonnegative P 1 z v.2) r)

lemma mixedDesignPremium_joint_integrable_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremium 1 z v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  exact integrable_mixedUnstoppedPremium_pow (k := k) P hbound known ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
    (c := fun _ => z) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hz)
    (fun i => (measurable_pi_apply i).comp measurable_snd)
    (hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)) r

lemma mixedScalarValue_integrable_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ^ r) (P.trainingCoordinateLaw k) :=
  integrable_mixedScalarValue_pow_unit (k := k) P hbound known (P.trainingCoordinateLaw k)
    (y := fun a => reservoirCoordinates.symm a) (c := fun _ => z)
    (fun i j => measurable_pi_apply (i, j)) measurable_const (fun _ => hz)
    (Filter.Eventually.of_forall (fun _ => le_refl z)) (trainingCoordinates_unit_ae P hbound) r

/-- Actual joint version of `upstat:bdg` for the second moment. -/
theorem Instance.mixedSuffixMoment_two_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedSuffixMoment known k z 2 ≤ (4 / (k : ℝ)) * P.mixedTruePremiumMoment known k z 1 := by
  have h := mixedSuffix_secondMoment_clocks (k := k) P known hbound hz
  have hXi : P.mixedSuffixMoment known k z 2 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 2
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (mixedSuffix_joint_integrable_pow P known hbound hz 2)
  have hU : P.mixedTruePremiumMoment known k z 1 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.mixedTruePremiumMoment, pow_one] using integral_prod_symm _ (mixedTruePremium_joint_integrable_pow (k := k) P known hbound hz 1)
  rw [← hXi, ← hU] at h
  exact h

/-- Actual joint version of `upstat:bdg` for the sixth moment. -/
theorem Instance.mixedSuffixMoment_six_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedSuffixMoment known k z 6 ≤ 2000000000 *
      (P.mixedTruePremiumMoment known k z 3 / (k : ℝ) ^ 3 + P.mixedTruePremiumMoment known k z 1 / (k : ℝ) ^ 5) := by
  have h := mixedSuffix_sixthMoment_clocks (k := k) P known hbound hz
  have hXi : P.mixedSuffixMoment known k z 6 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSuffixEnvelope P 1 z u ^ 6
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (mixedSuffix_joint_integrable_pow P known hbound hz 6)
  have hU3 : P.mixedTruePremiumMoment known k z 3 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ 3
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (mixedTruePremium_joint_integrable_pow P known hbound hz 3)
  have hU1 : P.mixedTruePremiumMoment known k z 1 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.mixedTruePremiumMoment, pow_one] using integral_prod_symm _ (mixedTruePremium_joint_integrable_pow (k := k) P known hbound hz 1)
  rw [← hXi, ← hU3, ← hU1] at h
  exact h

/-- Actual empirical-design Kac bound, then averaged over training. -/
theorem Instance.mixedDesignPremiumMoment_three_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedDesignPremiumMoment known k z 3 ≤ 13 * P.mixedScalarValueMoment known k z 3 := by
  have hI := mixedDesignPremium_joint_integrable_pow (k := k) P known hbound hz 3
  have hV := mixedScalarValue_integrable_pow (k := k) P known hbound hz 3
  rw [Instance.mixedDesignPremiumMoment, integral_prod _ hI]
  have h := integral_mono hI.integral_prod_left (hV.const_mul 13) (fun a =>
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremium_kac
      (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) (by norm_num : (0 : ℝ) < 1) hz |>.2)
  rw [integral_const_mul] at h
  exact h

end ProphetSecretary.Model
