import ProphetSecretary.Statistics.MixedEmpiricalSlopeSuffixMoments
import ProphetSecretary.Statistics.PremiumSlopeKac
import ProphetSecretary.Statistics.MixedEmpiricalPremiumRelations

/-!
# Joint mixed scalar-increment moments

Both scalar weights are fixed before training. Actual mixed premium centering,
monotonicity of the reoptimized value and generic Kac identities give a unit
mean and universal cubic budget, retaining the order of the independent
training and uniform-clock integrations.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.mixedSlopeSuffixMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z z' : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSlopeSuffixEnvelope P z z' v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.mixedSlopeTruePremiumMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z z' : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)), mixedTrueSlopePremiumSum P known z z' v.2 v.1 ^ r
    ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.mixedSlopeDesignPremiumMoment (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k] (z z' : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).premiumSlopeSum z z' v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

variable {k : ℕ} [NeZero k]

lemma Instance.mixedSlopeSuffixMoment_nonnegative (P : Instance n) (known : Finset (Fin n)) (z z' : ℝ) (r : ℕ) :
    0 ≤ P.mixedSlopeSuffixMoment known k z z' r := integral_nonneg (fun _ =>
      pow_nonneg (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _) r)

lemma mixedSlopeDesignPremium_joint_integrable_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).premiumSlopeSum z z' v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hm (c : ℝ) (hc : 0 ≤ c) : Measurable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremium 1 c v.2) :=
    measurable_mixedUnstoppedPremium (k := k) P (P.integrable_maximum_of_bounded hbound) known
      (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
      (c := fun _ => c) (u := Prod.snd)
      (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hc)
      (fun i => (measurable_pi_apply i).comp measurable_snd)
  apply Integrable.of_bound (((hm z hz).sub (hm z' (hz.trans hzz.le))).div_const (z' - z) |>.pow_const r).aestronglyMeasurable ((n : ℝ) ^ r)
  have hv : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (Instance.clocksLaw n) := measurePreserving_snd
  filter_upwards [hv.quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n := n))] with v hv
  have h := (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).premiumSlopeSum_bounds
    (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) hz hzz v.2 hv
  change ‖(mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).premiumSlopeSum z z' v.2 ^ r‖ ≤ (n : ℝ) ^ r
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h.1]
  exact pow_le_pow_left₀ h.1 h.2 r

lemma Instance.mixedSlopeTruePremiumMoment_one_eq (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeTruePremiumMoment known k z z' 1 =
      (P.mixedTruePremiumMoment known k z 1 - P.mixedTruePremiumMoment known k z' 1) / (z' - z) := by
  have hI (c : ℝ) (hc : 0 ≤ c) : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 c v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using mixedTruePremium_joint_integrable_pow (k := k) P known hbound hc 1
  simp only [Instance.mixedSlopeTruePremiumMoment, Instance.mixedTruePremiumMoment,
    mixedTrueSlopePremiumSum, pow_one, integral_div, integral_sub (hI z hz) (hI z' (hz.trans hzz.le))]

/-- Centering is used only at the two fixed weights, before taking their difference. -/
theorem Instance.mixedSlopeTruePremiumMoment_one_le_one (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeTruePremiumMoment known k z z' 1 ≤ 1 := by
  rw [P.mixedSlopeTruePremiumMoment_one_eq known hbound hz hzz]
  apply (div_le_one (sub_pos.mpr hzz)).mpr
  rw [P.mixedTruePremiumMoment_one_eq_value known hbound hz,
    P.mixedTruePremiumMoment_one_eq_value known hbound (hz.trans hzz.le)]
  have hm : P.mixedScalarValueMoment known k z 1 ≤ P.mixedScalarValueMoment known k z' 1 := by
    simp only [Instance.mixedScalarValueMoment, pow_one]
    apply integral_mono
      (by simpa only [pow_one] using mixedScalarValue_integrable_pow (k := k) P known hbound hz 1)
      (by simpa only [pow_one] using mixedScalarValue_integrable_pow (k := k) P known hbound (hz.trans hzz.le) 1)
    intro a
    exact optimalScalarValue_mono _ (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) zero_le_one hz le_rfl hzz.le
  linarith

/-- The design increment has a uniform cubic Kac budget after both experiments. -/
theorem Instance.mixedSlopeDesignPremiumMoment_three_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeDesignPremiumMoment known k z z' 3 ≤ 13 := by
  have hI := mixedSlopeDesignPremium_joint_integrable_pow (k := k) P known hbound hz hzz 3
  rw [Instance.mixedSlopeDesignPremiumMoment, integral_prod _ hI]
  have h := integral_mono hI.integral_prod_left (integrable_const (13 : ℝ)) (fun a =>
    ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).premiumSlopeSum_kac (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) hz hzz).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Actual joint version of `upstat:bdg` for the second moment. -/
theorem Instance.mixedSlopeSuffixMoment_two_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeSuffixMoment known k z z' 2 ≤ (4 / (k : ℝ)) * P.mixedSlopeTruePremiumMoment known k z z' 1 := by
  have h := mixedSlopeSuffix_secondMoment_clocks (k := k) P known hbound hz hzz
  have hXi : P.mixedSlopeSuffixMoment known k z z' 2 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 2
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (mixedSlopeSuffix_joint_integrable_pow P known hbound hz hzz 2)
  have hU : P.mixedSlopeTruePremiumMoment known k z z' 1 =
      ∫ u, (∫ a, mixedTrueSlopePremiumSum P known z z' u a
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.mixedSlopeTruePremiumMoment, pow_one] using integral_prod_symm _ (mixedTrueSlopePremium_joint_integrable_pow (k := k) P known hbound hz hzz 1)
  rw [← hXi, ← hU] at h
  exact h

/-- Actual joint version of `upstat:bdg` for the sixth moment. -/
theorem Instance.mixedSlopeSuffixMoment_six_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeSuffixMoment known k z z' 6 ≤ 2000000000 *
      (P.mixedSlopeTruePremiumMoment known k z z' 3 / (k : ℝ) ^ 3 + P.mixedSlopeTruePremiumMoment known k z z' 1 / (k : ℝ) ^ 5) := by
  have h := mixedSlopeSuffix_sixthMoment_clocks (k := k) P known hbound hz hzz
  have hXi : P.mixedSlopeSuffixMoment known k z z' 6 =
      ∫ u, (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 6
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (mixedSlopeSuffix_joint_integrable_pow P known hbound hz hzz 6)
  have hU3 : P.mixedSlopeTruePremiumMoment known k z z' 3 =
      ∫ u, (∫ a, mixedTrueSlopePremiumSum P known z z' u a ^ 3
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (mixedTrueSlopePremium_joint_integrable_pow P known hbound hz hzz 3)
  have hU1 : P.mixedSlopeTruePremiumMoment known k z z' 1 =
      ∫ u, (∫ a, mixedTrueSlopePremiumSum P known z z' u a
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.mixedSlopeTruePremiumMoment, pow_one] using integral_prod_symm _ (mixedTrueSlopePremium_joint_integrable_pow (k := k) P known hbound hz hzz 1)
  rw [← hXi, ← hU3, ← hU1] at h
  exact h


end ProphetSecretary.Model
