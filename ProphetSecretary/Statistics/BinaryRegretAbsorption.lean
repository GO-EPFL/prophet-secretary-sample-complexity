import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absorbing regret in the binary experiment

These explicit inequalities are the Young-inequality and modulus steps in
`thm:bayes`. They precede the asymptotic notation and retain every constant.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Statistics

lemma young_regret_bound {r z A : ℝ} (hr : 0 ≤ r) :
    -r + A * |z| * Real.sqrt r ≤ -r / 2 + (A ^ 2 / 2) * z ^ 2 := by
  have hs := Real.sq_sqrt hr
  have h := sq_nonneg (A * |z| - Real.sqrt r)
  have heq : (A * |z|) ^ 2 = A ^ 2 * z ^ 2 := by rw [mul_pow, sq_abs]
  nlinarith

/-- The modulus split at `2aBt`, valid for every nonnegative regret. -/
lemma bounded_modulus_regret_bound (ω : ℝ → ℝ) {r a B t : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hmono : Monotone ω) (hbound : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B) :
    -r / 2 + a * t * ω r ≤ a * t * ω (2 * a * B * t) := by
  have hat : 0 ≤ a * t := mul_nonneg ha ht
  have hlevel : 0 ≤ 2 * a * B * t := by positivity
  by_cases hsmall : r ≤ 2 * a * B * t
  · have h := mul_le_mul_of_nonneg_left (hmono hsmall) hat
    linarith
  · have hupper := mul_le_mul_of_nonneg_left (hbound r hr).2 hat
    have hnonneg := mul_nonneg hat (hbound (2 * a * B * t) hlevel).1
    nlinarith

def bayesModulusError (ω : ℝ → ℝ) (a B t : ℝ) : ℝ := a * t * ω (2 * a * B * t)

/-- The remaining regret contribution has an explicit bound that is `o(t)`.
The right-limit assumption is exactly the one used for nonnegative regret. -/
theorem bayesModulusError_littleO (ω : ℝ → ℝ) {a B : ℝ}
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hzero : ω 0 = 0)
    (hlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    bayesModulusError ω a B =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t) := by
  let k := 2 * a * B
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hcoef : Tendsto (fun t : ℝ => a * ω (k * t)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    by_cases hk : k = 0
    · simpa only [hk, zero_mul, hzero, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
      have hscale : Tendsto (fun t : ℝ => k * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have hcont : Continuous (fun t : ℝ => k * t) := continuous_const.mul continuous_id
          simpa only [mul_zero] using (hcont.tendsto 0).mono_left
            (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
        · have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
          exact hpos.mono fun t ht => mul_pos hkpos ht
      simpa only [mul_zero, Function.comp_def] using (hlim.comp hscale).const_mul a
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hcoef ε hε] with t ht
  have hsmall : |a * ω (k * t)| ≤ ε := by
    simpa only [Real.dist_eq, sub_zero] using ht.le
  have heq : |bayesModulusError ω a B t| = |a * ω (k * t)| * |t| := by
    rw [← abs_mul]
    congr 1
    dsimp [bayesModulusError, k]
    ring
  simpa only [Real.norm_eq_abs, heq] using mul_le_mul_of_nonneg_right hsmall (abs_nonneg t)

/-- The full pointwise regret bound used before averaging over training data. -/
theorem bayes_regret_absorption (ω : ℝ → ℝ) {δ r z K v b B t C : ℝ}
    (hr : 0 ≤ r) (hv : 0 ≤ v) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hmono : Monotone ω) (hbound : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B) :
    δ - r + K * v * |z| * Real.sqrt r - v * b * t + (1 + v) * t * ω r + C * t ^ 2 ≤
      δ - v * b * t + ((K * v) ^ 2 / 2) * z ^ 2 +
        bayesModulusError ω (1 + v) B t + C * t ^ 2 := by
  have hYoung := young_regret_bound (z := z) (A := K * v) hr
  have hMod := bounded_modulus_regret_bound ω hr (by linarith : 0 ≤ 1 + v) hB ht hmono hbound
  dsimp [bayesModulusError]
  linarith

end ProphetSecretary.Statistics
