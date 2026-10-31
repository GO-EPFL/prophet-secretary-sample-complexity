import ProphetSecretary.Analysis.AffineSlopeStability
import ProphetSecretary.Analysis.PointwiseDerivativeRegularity

/-!
# Square-root derivative bounds for nonnegative smooth functions

A common two-sided interval and derivative Lipschitz bound imply a uniform
square-root bound at zero. The exact zero-gap case follows from the same
quadratic inequality; no division by the gap or nonzero-gap hypothesis occurs.
-/
open Set
open scoped Topology
namespace ProphetSecretary.Analysis

lemma nonnegative_quadratic_slope_le_sqrt {r b U K : ℝ}
    (hr : 0 ≤ r) (hU : 0 ≤ U) (hrU : r ≤ U) (hK : 0 ≤ K)
    (hpay : ∀ t : ℝ, |t| ≤ 1 / 4 → 0 ≤ r + t * b + K * t ^ 2 / 2) :
    |b| ≤ Real.sqrt (4 * K + 64 * U + 2) * Real.sqrt r := by
  have hp := hpay (1 / 4) (by norm_num)
  have hn := hpay (-(1 / 4)) (by norm_num)
  have hB : 0 ≤ 4 * U + K / 8 := by positivity
  have hb : |b| ≤ 4 * U + K / 8 := by
    rw [abs_le]
    constructor <;> nlinarith only [hp,hn,hrU]
  have hstep (t : ℝ) (ht : |t| ≤ 1 / 4) : t * b ≤ r + K * t ^ 2 / 2 := by
    have h := hpay (-t) (by simpa only [abs_neg] using ht)
    nlinarith only [h]
  have h := slope_difference_le_sqrt hr hK hB (by norm_num : (0 : ℝ) < 1 / 4) hb hstep
  have heq : 2 * (K + 2 * (4 * U + K / 8) / (1 / 4) + 1) = 4 * K + 64 * U + 2 := by ring
  rwa [heq] at h

/-- Uniform derivative estimate used for both the global gap and a fixed
competitor's regret in `updual:derivative`. -/
theorem nonnegative_derivative_le_sqrt {f : ℝ → ℝ} {U Q : ℝ}
    (hU : 0 ≤ U) (hQ : 0 ≤ Q) (hbase : f 0 ≤ U)
    (hnonneg : ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4), 0 ≤ f t)
    (hf : ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4), HasDerivAt f (deriv f t) t)
    (hLip : ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ∀ s ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      |deriv f s - deriv f t| ≤ Q * |s - t|) :
    |deriv f 0| ≤ Real.sqrt (8 * Q + 64 * U + 2) * Real.sqrt (f 0) := by
  have hzero : (0 : ℝ) ∈ Icc (-(1 / 4) : ℝ) (1 / 4) := by norm_num
  have hL : LipschitzOnWith ⟨Q,hQ⟩ (deriv f) (Icc (-(1 / 4) : ℝ) (1 / 4)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro t ht s hs
    change |deriv f t - deriv f s| ≤ Q * |t - s|
    exact hLip s hs t ht
  have h := nonnegative_quadratic_slope_le_sqrt (hnonneg 0 hzero) hU hbase
    (by positivity : 0 ≤ 2 * Q) (b := deriv f 0) (K := 2 * Q) (by
      intro t ht
      have hmem : t ∈ Icc (-(1 / 4) : ℝ) (1 / 4) := abs_le.mp ht
      have hrem := quadratic_remainder_of_lipschitz_derivative hf hL hzero hmem
      simp only [sub_zero] at hrem
      change |f t - f 0 - deriv f 0 * t| ≤ Q * t ^ 2 at hrem
      have hu := (abs_le.mp hrem).2
      have hn := hnonneg t hmem
      nlinarith only [hu,hn])
  have heq : 4 * (2 * Q) + 64 * U + 2 = 8 * Q + 64 * U + 2 := by ring
  rwa [heq] at h

end ProphetSecretary.Analysis
