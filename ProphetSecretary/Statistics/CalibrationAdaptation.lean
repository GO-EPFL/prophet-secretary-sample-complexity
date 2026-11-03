import ProphetSecretary.Statistics.CalibrationNumericalTarget
import ProphetSecretary.Statistics.EmpiricalOptimismRate

/-!
# Empirical adaptation at a frozen true-law optimizer

The policy and scalar are chosen under the true instance before the independent
first sample block is drawn. The empirical optimum's advantage over this fixed
policy is nonnegative, and its mean is precisely the fixed-weight optimism.
This supplies the adaptation term in `lem:calibration-target`.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ} [NeZero m]

noncomputable def frozenAdaptation (π : RandomizedPolicy n) (lam : ℝ)
    (a : (Fin n × Fin m) → ℝ) : ℝ :=
  optimalScalarValue (trainingInstance a) lam (1-lam)-π.scalarObjective (trainingInstance a) lam (1-lam)

lemma frozenAdaptation_nonnegative (π : RandomizedPolicy n)
    {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) (a : (Fin n × Fin m) → ℝ) :
    0 ≤ frozenAdaptation π lam a :=
  sub_nonneg.mpr (scalarObjective_le_optimal π (trainingInstance a)
    (totalEmpiricalInstance_integrable _) hlam.1 (sub_nonneg.mpr hlam.2))

lemma normalized_value_difference_eq_scaled (π : RandomizedPolicy n) (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    optimalScalarValue Q lam (1-lam)-π.scalarObjective Q lam (1-lam) =
      lam*(optimalScalarValue Q 1 ((1-lam)/lam)-π.scalarObjective Q 1 ((1-lam)/lam)) := by
  have hz : 0 ≤ (1-lam)/lam := div_nonneg (sub_nonneg.mpr hlam.2) hlam.1.le
  have he : lam*((1-lam)/lam) = 1-lam := by field_simp [hlam.1.ne']
  have hV := optimalScalarValue_smul Q hQ (a := lam) (w := 1) (c := (1-lam)/lam)
    hlam.1.le zero_le_one hz
  have hJ := π.scalarObjective_smul Q hQ lam 1 ((1-lam)/lam)
  rw [mul_one, he] at hV hJ
  rw [hV, hJ]
  ring

lemma integrable_frozenAdaptation (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    Integrable (frozenAdaptation (m := m) π lam) (P.trainingCoordinateLaw m) := by
  let z := (1-lam)/lam
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hlam.2) hlam.1.le
  have hVI := integrable_empiricalScalarValue_unit (k := m) P hcap hz
  have hJI := (P.reservoirCoordinates_symm_measurePreserving m).integrable_comp_of_integrable
    (π.integrable_empiricalScalarObjective (k := m) P hcap z)
  have he : frozenAdaptation (m := m) π lam =
      fun a => lam*(optimalScalarValue (trainingInstance a) 1 z-π.scalarObjective (trainingInstance a) 1 z) := by
    funext a
    exact normalized_value_difference_eq_scaled π (trainingInstance a)
      (totalEmpiricalInstance_integrable _) hlam
  rw [he]
  exact (hVI.sub hJI).const_mul lam

/-- Expected adaptation is bounded by the checked fixed-weight empirical optimism. -/
theorem integral_frozenAdaptation_le (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    {lam lo hi : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hz : (1-lam)/lam ∈ Icc lo hi)
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam)) :
    (∫ a, frozenAdaptation (m := m) π lam a ∂P.trainingCoordinateLaw m) ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(m : ℝ) := by
  let z := (1-lam)/lam
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hlam.2) hlam.1.le
  have hP := P.integrable_maximum_of_bounded hcap
  have hVI := integrable_empiricalScalarValue_unit (k := m) P hcap hz0
  have hJI := (P.reservoirCoordinates_symm_measurePreserving m).integrable_comp_of_integrable
    (π.integrable_empiricalScalarObjective (k := m) P hcap z)
  have hOptRaw : π.scalarObjective P 1 z = optimalScalarValue P 1 z := by
    have he := normalized_value_difference_eq_scaled π P hP hlam
    rw [hOpt, sub_self] at he
    have hne := hlam.1.ne'
    have hzero : optimalScalarValue P 1 z-π.scalarObjective P 1 z = 0 := by
      exact (mul_eq_zero.mp he.symm).resolve_left hne
    linarith
  have hJmean : (∫ a : (Fin n × Fin m) → ℝ, π.scalarObjective (trainingInstance a) 1 z
      ∂P.trainingCoordinateLaw m) = optimalScalarValue P 1 z := by
    calc
      _ = ∫ y : Reservoir n m, π.scalarObjective (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw m :=
        (P.reservoirCoordinates_symm_measurePreserving m).integral_comp' _
      _ = π.scalarObjective P 1 z := π.integral_empiricalScalarObjective P hcap z
      _ = _ := hOptRaw
  have he : frozenAdaptation (m := m) π lam =
      fun a => lam*(optimalScalarValue (trainingInstance a) 1 z-π.scalarObjective (trainingInstance a) 1 z) := by
    funext a
    exact normalized_value_difference_eq_scaled π (trainingInstance a)
      (totalEmpiricalInstance_integrable _) hlam
  rw [he, integral_const_mul,
    integral_sub (f := fun a => optimalScalarValue (trainingInstance a) 1 z)
      (g := fun a => π.scalarObjective (trainingInstance a) 1 z) hVI hJI, hJmean]
  have hBias := (empiricalScalarValue_expected_optimism_bound (k := m) P hcap hlo hlohi hz).2
  have hScaled := mul_le_mul_of_nonneg_left hBias hlam.1.le
  have hR0 : 0 ≤ empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(m : ℝ) := by
    have hC := (empiricalCandidateRegretConstant_positive hlo hlohi).le
    have hS := P.totalFirstMoment_nonnegative
    positivity
  exact hScaled.trans (by nlinarith [mul_le_mul_of_nonneg_right hlam.2 hR0])

end ProphetSecretary.Statistics.Calibration
