import ProphetSecretary.Statistics.MixedEmpiricalUniformEnvelope
import ProphetSecretary.Statistics.MixedEmpiricalLocalizedMoments
import ProphetSecretary.Statistics.EmpiricalUniformLocalization

/-!
# Value-localized uniform moments with known laws

Uniformity is over physical scalars in [lo,hi] and every declared known-label
set. Remaining horizon u enters through [lo*u,hi*u]. Waiting bounds u in terms
of the true value, giving the same explicit interval-dependent constants
without dependence on instance size or horizon.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.mixedUniformResidualEnvelope_moment_endpoints (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    (∫ v, P.mixedUniformResidualEnvelope known k lo hi v ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      ProphetSecretary.Analysis.dyadicChainingConstant p *
        (P.mixedSuffixMoment known k lo p + P.mixedSuffixMoment known k hi p +
          empiricalIncrementMomentConstant k p * |hi - lo| ^ p) := by
  have h := (P.mixedUniformResidualEnvelope_moment (k := k) known hbound hp lo hi).2
  have he0 : (∫ v, |P.mixedIntervalEnvelope known k lo hi v 0| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = P.mixedSuffixMoment known k lo p := by
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [Instance.mixedIntervalEnvelope, mul_zero, add_zero, max_eq_right hlo]
    have h0 : 0 ≤ (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 lo v.2 :=
      ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
    rw [abs_of_nonneg h0]
  have he1 : (∫ v, |P.mixedIntervalEnvelope known k lo hi v 1| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = P.mixedSuffixMoment known k hi p := by
    apply integral_congr_ae
    filter_upwards [] with v
    have he : lo + (hi - lo) * 1 = hi := by ring
    rw [Instance.mixedIntervalEnvelope, he, max_eq_right (hlo.trans hlohi)]
    have h0 : 0 ≤ (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 hi v.2 :=
      ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
    rw [abs_of_nonneg h0]
  rw [he0, he1] at h
  exact h

/-- Uniform second moment in the manuscript's localized state `(A,u)`, with an
explicit constant depending only on the scalar interval. -/
theorem Instance.mixedUniformResidualEnvelope_two_localized (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi u a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hValue : optimalScalarValue P 1 (hi * u) ≤ a) :
    (∫ v, P.mixedUniformResidualEnvelope known k (lo * u) (hi * u) v ^ 2
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (18 * (128 + 4 * (hi - lo) ^ 2 / hi)) * (a / (k : ℝ) + 1 / (k : ℝ) ^ 2) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hc0 := mul_nonneg hlo hu0
  have hc1 := mul_nonneg hhi.le hu0
  have hc01 := mul_le_mul_of_nonneg_right hlohi hu0
  have hV0 : optimalScalarValue P 1 (lo * u) ≤ a :=
    (optimalScalarValue_mono P hP zero_le_one hc0 le_rfl hc01).trans hValue
  have hWait : hi * u ≤ a := (durationWeight_le_optimalScalarValue P hP zero_le_one hc1).trans hValue
  have hUSq : u ^ 2 ≤ a / hi := by
    have hule : u ≤ a / hi := (le_div_iff₀ hhi).mpr (by nlinarith)
    have huu : u ^ 2 ≤ u := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
    exact huu.trans hule
  have he0 : P.mixedSuffixMoment known k (lo * u) 2 ≤ 64 * (a / (k : ℝ) + 1 / (k : ℝ) ^ 2) :=
    (P.mixedSuffixMoment_localized known hbound hc0).1.trans (by gcongr)
  have he1 : P.mixedSuffixMoment known k (hi * u) 2 ≤ 64 * (a / (k : ℝ) + 1 / (k : ℝ) ^ 2) :=
    (P.mixedSuffixMoment_localized known hbound hc1).1.trans (by gcongr)
  have hB : empiricalIncrementMomentConstant k 2 * |hi * u - lo * u| ^ 2 ≤
      (4 * (hi - lo) ^ 2 / hi) * (a / (k : ℝ)) := by
    calc
      _ = (4 / (k : ℝ)) * (hi - lo) ^ 2 * u ^ 2 := by
        change (4 / (k : ℝ)) * |hi * u - lo * u| ^ 2 = _
        rw [← sub_mul, abs_mul, mul_pow, sq_abs, sq_abs]
        ring
      _ ≤ (4 / (k : ℝ)) * (hi - lo) ^ 2 * (a / hi) := by gcongr
      _ = _ := by ring
  have h := P.mixedUniformResidualEnvelope_moment_endpoints (k := k) known hbound (Or.inl rfl) hc0 hc01
  rw [ProphetSecretary.Analysis.dyadicChainingConstant_two] at h
  convert ProphetSecretary.Statistics.localize_two_endpoints (A := 64) (C := 18)
    (by norm_num) (div_nonneg (by positivity) hhi.le)
    (by positivity : 0 ≤ 1 / (k : ℝ) ^ 2) h he0 he1 hB using 1; norm_num

/-- Uniform sixth moment in the manuscript's localized state `(A,u)`, with an
explicit constant depending only on the scalar interval. -/
theorem Instance.mixedUniformResidualEnvelope_six_localized (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi u a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hValue : optimalScalarValue P 1 (hi * u) ≤ a) :
    (∫ v, P.mixedUniformResidualEnvelope known k (lo * u) (hi * u) v ^ 6
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (23328 * (2 * (6672000000000 ^ 2 + 13348000000000) +
        (106000000000 ^ 2 + 212000000000) * (hi - lo) ^ 6 / hi ^ 3)) *
        (a ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hc0 := mul_nonneg hlo hu0
  have hc1 := mul_nonneg hhi.le hu0
  have hc01 := mul_le_mul_of_nonneg_right hlohi hu0
  have hV0 : optimalScalarValue P 1 (lo * u) ≤ a :=
    (optimalScalarValue_mono P hP zero_le_one hc0 le_rfl hc01).trans hValue
  have hWait : hi * u ≤ a := (durationWeight_le_optimalScalarValue P hP zero_le_one hc1).trans hValue
  have hUSq : u ^ 2 ≤ a / hi := by
    have hule : u ≤ a / hi := (le_div_iff₀ hhi).mpr (by nlinarith)
    have huu : u ^ 2 ≤ u := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
    exact huu.trans hule
  have hUSix : u ^ 6 ≤ (a / hi) ^ 3 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg u) hUSq 3
  have hV00 := optimalScalarValue_nonnegative P hP zero_le_one hc0
  have hV10 := optimalScalarValue_nonnegative P hP zero_le_one hc1
  have he0 : P.mixedSuffixMoment known k (lo * u) 6 ≤
      (6672000000000 ^ 2 + 13348000000000) * (a ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) :=
    (P.mixedSuffixMoment_localized known hbound hc0).2.trans (by gcongr)
  have he1 : P.mixedSuffixMoment known k (hi * u) 6 ≤
      (6672000000000 ^ 2 + 13348000000000) * (a ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) :=
    (P.mixedSuffixMoment_localized known hbound hc1).2.trans (by gcongr)
  have hB : empiricalIncrementMomentConstant k 6 * |hi * u - lo * u| ^ 6 ≤
      ((106000000000 ^ 2 + 212000000000) * (hi - lo) ^ 6 / hi ^ 3) * (a ^ 3 / (k : ℝ) ^ 3) := by
    calc
      _ = ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * (hi - lo) ^ 6 * u ^ 6 := by
        change ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * |hi * u - lo * u| ^ 6 = _
        rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlohi), abs_of_nonneg hu0, mul_pow]
        ring
      _ ≤ ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * (hi - lo) ^ 6 * (a / hi) ^ 3 := by gcongr
      _ = _ := by rw [div_pow]; ring
  have h := P.mixedUniformResidualEnvelope_moment_endpoints (k := k) known hbound (Or.inr rfl) hc0 hc01
  rw [ProphetSecretary.Analysis.dyadicChainingConstant_six] at h
  exact ProphetSecretary.Statistics.localize_two_endpoints
    (A := (6672000000000 ^ 2 + 13348000000000 : ℝ)) (C := 23328)
    (by norm_num) (div_nonneg (by positivity) (pow_nonneg hhi.le 3))
    (by positivity : 0 ≤ 1 / (k : ℝ) ^ 6) h he0 he1 hB

end ProphetSecretary.Model
