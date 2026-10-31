import ProphetSecretary.Statistics.EmpiricalUniformEnvelope
import ProphetSecretary.Statistics.EmpiricalLocalizedMoments

/-!
# Value-localized uniform empirical moments

For physical scalar weights in `[lo,hi]` and remaining horizon `u`, the empirical
residual envelope is uniform over the interval `[lo*u,hi*u]`. Endpoint localization
and `hi*u ≤ V(P;1,hi*u)` give constants depending only on the scalar interval,
independent of instance size and horizon.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics

lemma localize_two_endpoints {E e₀ e₁ b A B C r q : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hE : E ≤ C * (e₀ + e₁ + b)) (he₀ : e₀ ≤ A * (r + q)) (he₁ : e₁ ≤ A * (r + q)) (hb : b ≤ B * r) :
    E ≤ (C * (2 * A + B)) * (r + q) := by
  apply hE.trans
  have hsum : e₀ + e₁ + b ≤ (2 * A + B) * (r + q) := by nlinarith [mul_nonneg hB hq]
  exact (mul_le_mul_of_nonneg_left hsum hC).trans_eq (by ring)

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.empiricalUniformResidualEnvelope_moment_endpoints (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    (∫ v, P.empiricalUniformResidualEnvelope k lo hi v ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      ProphetSecretary.Analysis.dyadicChainingConstant p *
        (P.empiricalSuffixMoment k lo p + P.empiricalSuffixMoment k hi p +
          empiricalIncrementMomentConstant k p * |hi - lo| ^ p) := by
  have h := (P.empiricalUniformResidualEnvelope_moment (k := k) hbound hp lo hi).2
  have he0 : (∫ v, |P.empiricalIntervalEnvelope k lo hi v 0| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = P.empiricalSuffixMoment k lo p := by
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [Instance.empiricalIntervalEnvelope, mul_zero, add_zero, max_eq_right hlo]
    have h0 : 0 ≤ (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 lo v.2 :=
      ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
    rw [abs_of_nonneg h0]
  have he1 : (∫ v, |P.empiricalIntervalEnvelope k lo hi v 1| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = P.empiricalSuffixMoment k hi p := by
    apply integral_congr_ae
    filter_upwards [] with v
    have he : lo + (hi - lo) * 1 = hi := by ring
    rw [Instance.empiricalIntervalEnvelope, he, max_eq_right (hlo.trans hlohi)]
    have h0 : 0 ≤ (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 hi v.2 :=
      ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
    rw [abs_of_nonneg h0]
  rw [he0, he1] at h
  exact h

/-- Uniform second moment in the manuscript's localized state `(A,u)`, with an
explicit constant depending only on the scalar interval. -/
theorem Instance.empiricalUniformResidualEnvelope_two_localized (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi u a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hValue : optimalScalarValue P 1 (hi * u) ≤ a) :
    (∫ v, P.empiricalUniformResidualEnvelope k (lo * u) (hi * u) v ^ 2
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
  have he0 : P.empiricalSuffixMoment k (lo * u) 2 ≤ 64 * (a / (k : ℝ) + 1 / (k : ℝ) ^ 2) :=
    (P.empiricalSuffixMoment_localized hbound hc0).1.trans (by gcongr)
  have he1 : P.empiricalSuffixMoment k (hi * u) 2 ≤ 64 * (a / (k : ℝ) + 1 / (k : ℝ) ^ 2) :=
    (P.empiricalSuffixMoment_localized hbound hc1).1.trans (by gcongr)
  have hB : empiricalIncrementMomentConstant k 2 * |hi * u - lo * u| ^ 2 ≤
      (4 * (hi - lo) ^ 2 / hi) * (a / (k : ℝ)) := by
    calc
      _ = (4 / (k : ℝ)) * (hi - lo) ^ 2 * u ^ 2 := by
        change (4 / (k : ℝ)) * |hi * u - lo * u| ^ 2 = _
        rw [← sub_mul, abs_mul, mul_pow, sq_abs, sq_abs]
        ring
      _ ≤ (4 / (k : ℝ)) * (hi - lo) ^ 2 * (a / hi) := by gcongr
      _ = _ := by ring
  have h := P.empiricalUniformResidualEnvelope_moment_endpoints (k := k) hbound (Or.inl rfl) hc0 hc01
  rw [ProphetSecretary.Analysis.dyadicChainingConstant_two] at h
  convert ProphetSecretary.Statistics.localize_two_endpoints (A := 64) (C := 18)
    (by norm_num) (div_nonneg (by positivity) hhi.le)
    (by positivity : 0 ≤ 1 / (k : ℝ) ^ 2) h he0 he1 hB using 1; norm_num

/-- Uniform sixth moment in the manuscript's localized state `(A,u)`, with an
explicit constant depending only on the scalar interval. -/
theorem Instance.empiricalUniformResidualEnvelope_six_localized (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi u a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hValue : optimalScalarValue P 1 (hi * u) ≤ a) :
    (∫ v, P.empiricalUniformResidualEnvelope k (lo * u) (hi * u) v ^ 6
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
  have he0 : P.empiricalSuffixMoment k (lo * u) 6 ≤
      (6672000000000 ^ 2 + 13348000000000) * (a ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) :=
    (P.empiricalSuffixMoment_localized hbound hc0).2.trans (by gcongr)
  have he1 : P.empiricalSuffixMoment k (hi * u) 6 ≤
      (6672000000000 ^ 2 + 13348000000000) * (a ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) :=
    (P.empiricalSuffixMoment_localized hbound hc1).2.trans (by gcongr)
  have hB : empiricalIncrementMomentConstant k 6 * |hi * u - lo * u| ^ 6 ≤
      ((106000000000 ^ 2 + 212000000000) * (hi - lo) ^ 6 / hi ^ 3) * (a ^ 3 / (k : ℝ) ^ 3) := by
    calc
      _ = ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * (hi - lo) ^ 6 * u ^ 6 := by
        change ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * |hi * u - lo * u| ^ 6 = _
        rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlohi), abs_of_nonneg hu0, mul_pow]
        ring
      _ ≤ ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * (hi - lo) ^ 6 * (a / hi) ^ 3 := by gcongr
      _ = _ := by rw [div_pow]; ring
  have h := P.empiricalUniformResidualEnvelope_moment_endpoints (k := k) hbound (Or.inr rfl) hc0 hc01
  rw [ProphetSecretary.Analysis.dyadicChainingConstant_six] at h
  exact ProphetSecretary.Statistics.localize_two_endpoints
    (A := (6672000000000 ^ 2 + 13348000000000 : ℝ)) (C := 23328)
    (by norm_num) (div_nonneg (by positivity) (pow_nonneg hhi.le 3))
    (by positivity : 0 ≤ 1 / (k : ℝ) ^ 6) h he0 he1 hB

end ProphetSecretary.Model
