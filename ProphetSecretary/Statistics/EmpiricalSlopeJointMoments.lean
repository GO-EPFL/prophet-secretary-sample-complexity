import ProphetSecretary.Statistics.EmpiricalSlopeSuffixMoments
import ProphetSecretary.Statistics.PremiumSlopeKac
import ProphetSecretary.Statistics.EmpiricalPremiumRelations

/-!
# Joint moments of normalized scalar increments

Both weights are fixed before training. The true-law and design-law premium sums
are integrated over independent training and uniform clocks. The exact empirical
premium means imply a deterministic unit budget after averaging.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.empiricalSlopeSuffixMoment (P : Instance n) (k : ℕ) [NeZero k] (z z' : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSlopeSuffixEnvelope P z z' v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.empiricalSlopeTruePremiumMoment (P : Instance n) (k : ℕ) [NeZero k] (z z' : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)), empiricalTrueSlopePremiumSum P z z' v.2 v.1 ^ r
    ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

noncomputable def Instance.empiricalSlopeDesignPremiumMoment (P : Instance n) (k : ℕ) [NeZero k] (z z' : ℝ) (r : ℕ) : ℝ :=
  ∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
    (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).premiumSlopeSum z z' v.2 ^ r
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)

variable {k : ℕ} [NeZero k]

lemma Instance.empiricalSlopeSuffixMoment_nonnegative (P : Instance n) (z z' : ℝ) (r : ℕ) :
    0 ≤ P.empiricalSlopeSuffixMoment k z z' r := integral_nonneg (fun _ =>
      pow_nonneg (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _) r)

lemma empiricalSlopeDesignPremium_joint_integrable_pow (P : Instance n)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (r : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).premiumSlopeSum z z' v.2 ^ r)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hm (c : ℝ) (hc : 0 ≤ c) : Measurable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremium 1 c v.2) :=
    measurable_empiricalUnstoppedPremium (k := k)
      (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
      (c := fun _ => c) (u := Prod.snd)
      (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hc)
      (fun i => (measurable_pi_apply i).comp measurable_snd)
  apply Integrable.of_bound (((hm z hz).sub (hm z' (hz.trans hzz.le))).div_const (z' - z) |>.pow_const r).aestronglyMeasurable ((n : ℝ) ^ r)
  have hv : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (Instance.clocksLaw n) := measurePreserving_snd
  filter_upwards [hv.quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n := n))] with v hv
  have h := (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).premiumSlopeSum_bounds
    (totalEmpiricalInstance_integrable _) hz hzz v.2 hv
  change ‖(totalEmpiricalInstance (reservoirCoordinates.symm v.1)).premiumSlopeSum z z' v.2 ^ r‖ ≤ (n : ℝ) ^ r
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h.1]
  exact pow_le_pow_left₀ h.1 h.2 r

lemma Instance.empiricalSlopeTruePremiumMoment_one_eq (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeTruePremiumMoment k z z' 1 =
      (P.empiricalTruePremiumMoment k z 1 - P.empiricalTruePremiumMoment k z' 1) / (z' - z) := by
  have hI (c : ℝ) (hc : 0 ≤ c) : Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder P 1 c v.2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
    simpa only [pow_one] using empiricalTruePremium_joint_integrable_pow (k := k) P hbound hc 1
  simp only [Instance.empiricalSlopeTruePremiumMoment, Instance.empiricalTruePremiumMoment,
    empiricalTrueSlopePremiumSum, pow_one, integral_div, integral_sub (hI z hz) (hI z' (hz.trans hzz.le))]

/-- Centering is used only at the two fixed weights, before taking their difference. -/
theorem Instance.empiricalSlopeTruePremiumMoment_one_le_one (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeTruePremiumMoment k z z' 1 ≤ 1 := by
  rw [P.empiricalSlopeTruePremiumMoment_one_eq hbound hz hzz]
  apply (div_le_one (sub_pos.mpr hzz)).mpr
  rw [P.empiricalTruePremiumMoment_one_eq_value hbound hz,
    P.empiricalTruePremiumMoment_one_eq_value hbound (hz.trans hzz.le)]
  have hm : P.empiricalScalarValueMoment k z 1 ≤ P.empiricalScalarValueMoment k z' 1 := by
    simp only [Instance.empiricalScalarValueMoment, pow_one]
    apply integral_mono
      (by simpa only [pow_one] using empiricalScalarValue_integrable_pow (k := k) P hbound hz 1)
      (by simpa only [pow_one] using empiricalScalarValue_integrable_pow (k := k) P hbound (hz.trans hzz.le) 1)
    intro a
    exact optimalScalarValue_mono _ (totalEmpiricalInstance_integrable _) zero_le_one hz le_rfl hzz.le
  linarith

/-- The design increment has a uniform cubic Kac budget after both experiments. -/
theorem Instance.empiricalSlopeDesignPremiumMoment_three_le (P : Instance n)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeDesignPremiumMoment k z z' 3 ≤ 13 := by
  have hI := empiricalSlopeDesignPremium_joint_integrable_pow (k := k) P hz hzz 3
  rw [Instance.empiricalSlopeDesignPremiumMoment, integral_prod _ hI]
  have h := integral_mono hI.integral_prod_left (integrable_const (13 : ℝ)) (fun a =>
    ((totalEmpiricalInstance (reservoirCoordinates.symm a)).premiumSlopeSum_kac (totalEmpiricalInstance_integrable _) hz hzz).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Actual joint version of `upstat:bdg` for the second moment. -/
theorem Instance.empiricalSlopeSuffixMoment_two_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeSuffixMoment k z z' 2 ≤ (4 / (k : ℝ)) * P.empiricalSlopeTruePremiumMoment k z z' 1 := by
  have h := empiricalSlopeSuffix_secondMoment_clocks (k := k) P hbound hz hzz
  have hXi : P.empiricalSlopeSuffixMoment k z z' 2 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 2
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (empiricalSlopeSuffix_joint_integrable_pow P hbound hz hzz 2)
  have hU : P.empiricalSlopeTruePremiumMoment k z z' 1 =
      ∫ u, (∫ a, empiricalTrueSlopePremiumSum P z z' u a
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.empiricalSlopeTruePremiumMoment, pow_one] using integral_prod_symm _ (empiricalTrueSlopePremium_joint_integrable_pow (k := k) P hbound hz hzz 1)
  rw [← hXi, ← hU] at h
  exact h

/-- Actual joint version of `upstat:bdg` for the sixth moment. -/
theorem Instance.empiricalSlopeSuffixMoment_six_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeSuffixMoment k z z' 6 ≤ 2000000000 *
      (P.empiricalSlopeTruePremiumMoment k z z' 3 / (k : ℝ) ^ 3 + P.empiricalSlopeTruePremiumMoment k z z' 1 / (k : ℝ) ^ 5) := by
  have h := empiricalSlopeSuffix_sixthMoment_clocks (k := k) P hbound hz hzz
  have hXi : P.empiricalSlopeSuffixMoment k z z' 6 =
      ∫ u, (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).residualSlopeSuffixEnvelope P z z' u ^ 6
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (empiricalSlopeSuffix_joint_integrable_pow P hbound hz hzz 6)
  have hU3 : P.empiricalSlopeTruePremiumMoment k z z' 3 =
      ∫ u, (∫ a, empiricalTrueSlopePremiumSum P z z' u a ^ 3
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n :=
    integral_prod_symm _ (empiricalTrueSlopePremium_joint_integrable_pow P hbound hz hzz 3)
  have hU1 : P.empiricalSlopeTruePremiumMoment k z z' 1 =
      ∫ u, (∫ a, empiricalTrueSlopePremiumSum P z z' u a
        ∂P.trainingCoordinateLaw k) ∂Instance.clocksLaw n := by
    simpa only [Instance.empiricalSlopeTruePremiumMoment, pow_one] using integral_prod_symm _ (empiricalTrueSlopePremium_joint_integrable_pow (k := k) P hbound hz hzz 1)
  rw [← hXi, ← hU3, ← hU1] at h
  exact h


end ProphetSecretary.Model
