import ProphetSecretary.Model.ScalarRatio

/-!
# Comparison of instance scalar ratios for duration calibration

The true-law minimizing weight is fixed before training. Testing the empirical
ratio at that weight bounds its upward error by one scalar numerator. These
are the deterministic ratio steps of `lem:calibration-target`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- The benchmark denominator retains a lower bound shared by `M` and one. -/
lemma Instance.scalarRatio_denominator_ge (Q : Instance n) {eta lam : ℝ}
    (hEta : eta ≤ 1) (hM : eta ≤ Q.expectedMaximum)
    (hlam : lam ∈ Icc (0 : ℝ) 1) :
    eta ≤ lam*Q.expectedMaximum+1-lam := by
  have hR := mul_le_mul_of_nonneg_left hM hlam.1
  have hD := mul_le_mul_of_nonneg_left hEta (sub_nonneg.mpr hlam.2)
  nlinarith

/-- Testing one fixed normalized weight upper-bounds the difference of instance ratios. -/
lemma Instance.scalarRatio_difference_le (P Q : Instance n)
    (hQ : Q.HasPositiveFiniteMaximum) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    Q.optimalScalarRatio-P.optimalScalarRatio ≤
      (optimalScalarValue Q lam (1-lam)-P.optimalScalarRatio*
        (lam*Q.expectedMaximum+1-lam)) / (lam*Q.expectedMaximum+1-lam) := by
  have h := Q.optimalScalarRatio_le_at hQ hlam
  unfold Instance.normalizedScalarRatio at h
  have he : optimalScalarValue Q lam (1-lam)/(lam*Q.expectedMaximum+1-lam)-
      P.optimalScalarRatio =
      (optimalScalarValue Q lam (1-lam)-P.optimalScalarRatio*
        (lam*Q.expectedMaximum+1-lam)) / (lam*Q.expectedMaximum+1-lam) := by
    field_simp [(Q.scalarRatio_denominator_pos hQ.2 hlam).ne']
  exact (sub_le_sub_right h P.optimalScalarRatio).trans_eq he

/-- Scalar slack absorbs the ratio slack with the same deterministic weight. -/
lemma Instance.scalarGap_ratioSlack_absorption (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    (1/lam)*normalizedScalarGap P lam - ((1-lam)/lam)*
      (P.optimalScalarRatio-optimalCompetitiveRatio) ≥
      (P.expectedMaximum/(lam*P.expectedMaximum+1-lam))*normalizedScalarGap P lam := by
  have h01 : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.1.le, hlam.2⟩
  have hB := P.ratioSlack_mul_benchmark_le_gap hP h01
  have hD := P.scalarRatio_denominator_pos hP.2 h01
  have hL : 0 ≤ (1-lam)/lam := div_nonneg (sub_nonneg.mpr hlam.2) hlam.1.le
  have hRatio : (P.expectedMaximum/(lam*P.expectedMaximum+1-lam))*normalizedScalarGap P lam =
      (P.expectedMaximum*normalizedScalarGap P lam)/(lam*P.expectedMaximum+1-lam) := by ring
  rw [hRatio]
  apply (div_le_iff₀ hD).mpr
  have he : ((1/lam)*normalizedScalarGap P lam - ((1-lam)/lam)*
      (P.optimalScalarRatio-optimalCompetitiveRatio))*(lam*P.expectedMaximum+1-lam) -
      P.expectedMaximum*normalizedScalarGap P lam =
      ((1-lam)/lam)*(normalizedScalarGap P lam -
        (P.optimalScalarRatio-optimalCompetitiveRatio)*(lam*P.expectedMaximum+1-lam)) := by
    field_simp [hlam.1.ne']
    ring
  have hNonneg : 0 ≤ ((1-lam)/lam)*(normalizedScalarGap P lam -
      (P.optimalScalarRatio-optimalCompetitiveRatio)*(lam*P.expectedMaximum+1-lam)) :=
    mul_nonneg hL (sub_nonneg.mpr hB)
  rw [← he] at hNonneg
  linarith

/-- The ratio numerator separates the frozen policy kernel, adaptation gain,
and expected-maximum error at the true minimizing weight. -/
lemma RandomizedPolicy.calibrationRatio_numerator_decomposition (π : RandomizedPolicy n)
    (P Q : Instance n) (hP : P.HasPositiveFiniteMaximum)
    {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1)
    (hmin : P.optimalScalarRatio = P.normalizedScalarRatio lam) :
    optimalScalarValue Q lam (1-lam)-P.optimalScalarRatio*(lam*Q.expectedMaximum+1-lam) =
      (π.scalarObjective Q lam (1-lam)-optimalCompetitiveRatio*(lam*Q.expectedMaximum+1-lam)) -
      normalizedScalarGap P lam +
      (optimalScalarValue Q lam (1-lam)-π.scalarObjective Q lam (1-lam)) -
      (P.optimalScalarRatio-optimalCompetitiveRatio)*lam*(Q.expectedMaximum-P.expectedMaximum) := by
  rw [P.normalizedScalarGap_at_ratio_minimizer hP hlam hmin]
  ring

end ProphetSecretary.Model
