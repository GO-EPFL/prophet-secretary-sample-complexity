import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import ProphetSecretary.Reach.ReachIntegralBounds

/-!
# Explicit empirical moment absorption

These numerical inequalities retain all constants before deriving localized rates.
The square-root term is absorbed by a polynomial Young inequality.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics

lemma absorb_second_moment {H k A B v : ℝ} (hH : 0 ≤ H) (hk : 0 < k)
    (h : H ≤ (A * v + B * Real.sqrt H) / k) :
    H ≤ 2 * A * v / k + B ^ 2 / k ^ 2 := by
  have hm : H * k ≤ A * v + B * Real.sqrt H := (le_div_iff₀ hk).mp h
  have hmk := mul_le_mul_of_nonneg_right hm hk.le
  have hs : (k * Real.sqrt H) ^ 2 = k ^ 2 * H := by rw [mul_pow, Real.sq_sqrt hH]
  have hden : H * k ^ 2 ≤ 2 * A * v * k + B ^ 2 := by
    nlinarith [sq_nonneg (k * Real.sqrt H - B)]
  calc
    H ≤ (2 * A * v * k + B ^ 2) / k ^ 2 := (le_div_iff₀ (pow_pos hk 2)).mpr hden
    _ = _ := by field_simp

lemma absorb_sixth_moment {H k A B v : ℝ} (hH : 0 ≤ H) (hk : 0 < k)
    (h : H ≤ A * v ^ 3 / k ^ 3 + A * Real.sqrt H / k ^ 3 + B / k ^ 6) :
    H ≤ 2 * A * v ^ 3 / k ^ 3 + (A ^ 2 + 2 * B) / k ^ 6 := by
  have he : A * v ^ 3 / k ^ 3 + A * Real.sqrt H / k ^ 3 + B / k ^ 6 =
      (A * v ^ 3 * k ^ 3 + A * k ^ 3 * Real.sqrt H + B) / k ^ 6 := by field_simp
  rw [he] at h
  have hm := (le_div_iff₀ (pow_pos hk 6)).mp h
  have hs : (k ^ 3 * Real.sqrt H) ^ 2 = k ^ 6 * H := by rw [mul_pow, Real.sq_sqrt hH]; ring
  have hden : H * k ^ 6 ≤ 2 * A * v ^ 3 * k ^ 3 + A ^ 2 + 2 * B := by
    nlinarith [sq_nonneg (k ^ 3 * Real.sqrt H - A)]
  calc
    H ≤ (2 * A * v ^ 3 * k ^ 3 + A ^ 2 + 2 * B) / k ^ 6 := (le_div_iff₀ (pow_pos hk 6)).mpr hden
    _ = _ := by field_simp; ring

/-- The first-moment jump term is absorbed into the cubic localization scale. -/
lemma first_over_fifth_le_cube_over_third {v k : ℝ} (hv : 0 ≤ v) (hk : 0 < k) :
    v / k ^ 5 ≤ v ^ 3 / k ^ 3 + 1 / k ^ 6 := by
  let t := k * v
  have ht : 0 ≤ t := mul_nonneg hk.le hv
  have h : t ≤ t ^ 3 + 1 := by
    by_cases h1 : t ≤ 1
    · nlinarith [pow_nonneg ht 3]
    · have h1 : 1 ≤ t := le_of_not_ge h1
      have h2 : t ≤ t ^ 2 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr h1)]
      have h3 : t ^ 2 ≤ t ^ 3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr h1)]
      linarith
  calc
    v / k ^ 5 = t / k ^ 6 := by dsimp [t]; field_simp
    _ ≤ (t ^ 3 + 1) / k ^ 6 := div_le_div_of_nonneg_right h (pow_nonneg hk.le 6)
    _ = v ^ 3 / k ^ 3 + 1 / k ^ 6 := by dsimp [t]; field_simp

lemma cube_add_le_four_cubes {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * a ^ 3 + 4 * b ^ 3 := by
  have h : 0 ≤ (a - b) ^ 2 * (a + b) := mul_nonneg (sq_nonneg _) (add_nonneg ha hb)
  nlinarith

section Jensen

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma cube_integral_le_integral_cube {f : Ω → ℝ} (h0 : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hf : Integrable f μ) (hf3 : Integrable (fun ω => f ω ^ 3) μ) :
    (∫ ω, f ω ∂μ) ^ 3 ≤ ∫ ω, f ω ^ 3 ∂μ := by
  exact (convexOn_pow (𝕜 := ℝ) 3).map_integral_le (continuous_id.pow 3).continuousOn isClosed_Ici h0 hf
    (by simpa only [Function.comp_def] using hf3)

lemma integral_le_sqrt_second {f : Ω → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, f ω ∂μ) ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) :=
  Real.le_sqrt_of_sq_le (ProphetSecretary.Reach.sq_integral_le_integral_sq μ hf hf2)

lemma integral_cube_le_sqrt_sixth {f : Ω → ℝ} (hf3 : Integrable (fun ω => f ω ^ 3) μ)
    (hf6 : Integrable (fun ω => f ω ^ 6) μ) :
    (∫ ω, f ω ^ 3 ∂μ) ≤ Real.sqrt (∫ ω, f ω ^ 6 ∂μ) := by
  have h := integral_le_sqrt_second μ hf3 (by simpa only [← pow_mul] using hf6)
  simpa only [← pow_mul] using h

end Jensen

end ProphetSecretary.Statistics
