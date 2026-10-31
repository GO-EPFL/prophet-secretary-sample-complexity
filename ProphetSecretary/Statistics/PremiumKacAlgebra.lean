import ProphetSecretary.Statistics.PremiumMean

/-!
# Algebra for positive-premium moments

The quadratic and cubic expansions and their explicit numerical recursion bounds
supply the constants three and thirteen in paper `upstat:kac`.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics

lemma kac_quadratic_step {a b s v r2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hs : 0 ≤ s) (_hv : 0 ≤ v) (hav : a ≤ v) (hbs : b ≤ s) (hsv : s ≤ v)
    (hr2 : r2 ≤ 3 * s * b) :
    a ^ 2 + 2 * a * b + r2 ≤ 3 * v * (a + b) := by
  have haa : a ^ 2 ≤ v * a := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hav)]
  have hab : a * b ≤ v * a := by nlinarith [mul_le_mul_of_nonneg_left (hbs.trans hsv) ha]
  have hrs : 3 * s * b ≤ 3 * v * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsv (by norm_num)) hb
  nlinarith

lemma kac_cubic_step {a b s v r2 r3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hav : a ≤ v) (hbs : b ≤ s) (hsv : s ≤ v)
    (hr2 : r2 ≤ 3 * s * b) (hr3 : r3 ≤ 13 * s ^ 2 * b) :
    a ^ 3 + 3 * a ^ 2 * b + 3 * a * r2 + r3 ≤ 13 * v ^ 2 * (a + b) := by
  have hab : a * b ≤ v ^ 2 := (mul_le_mul hav (hbs.trans hsv) hb hv).trans_eq (by ring)
  have hsb : s * b ≤ v ^ 2 := (mul_le_mul hsv (hbs.trans hsv) hb hv).trans_eq (by ring)
  have haa : a ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ha hv).mpr hav
  have hss : s ^ 2 ≤ v ^ 2 := (sq_le_sq₀ hs hv).mpr hsv
  have ha3 : a ^ 3 ≤ v ^ 2 * a := by
    simpa only [pow_succ] using mul_le_mul_of_nonneg_right haa ha
  have ha2b : a ^ 2 * b ≤ v ^ 2 * a := by
    nlinarith [mul_le_mul_of_nonneg_left hab ha]
  have hcross : 3 * a * r2 ≤ 9 * v ^ 2 * a := by
    calc
      _ ≤ 3 * a * (3 * s * b) := mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = 9 * a * (s * b) := by ring
      _ ≤ 9 * a * v ^ 2 := mul_le_mul_of_nonneg_left hsb (by positivity)
      _ = _ := by ring
  have hlast : r3 ≤ 13 * v ^ 2 * b := hr3.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hss (by norm_num)) hb)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma integral_const_add_pow_two (a : ℝ) {B : Ω → ℝ}
    (hB : Integrable B μ) (hB2 : Integrable (fun ω => B ω ^ 2) μ) :
    (∫ ω, (a + B ω) ^ 2 ∂μ) = a ^ 2 + 2 * a * (∫ ω, B ω ∂μ) + ∫ ω, B ω ^ 2 ∂μ := by
  have he : (fun ω => (a + B ω) ^ 2) = (fun ω => (a ^ 2 + 2 * a * B ω) + B ω ^ 2) := by
    funext ω
    ring
  rw [he,
    integral_add (f := fun ω => a ^ 2 + 2 * a * B ω) (g := fun ω => B ω ^ 2)
      ((integrable_const _).add (hB.const_mul (2 * a))) hB2,
    integral_add (f := fun _ : Ω => a ^ 2) (g := fun ω => 2 * a * B ω)
      (integrable_const _) (hB.const_mul (2 * a)),
    integral_const, probReal_univ, one_smul, integral_const_mul]

lemma integral_const_add_pow_three (a : ℝ) {B : Ω → ℝ}
    (hB : Integrable B μ) (hB2 : Integrable (fun ω => B ω ^ 2) μ)
    (hB3 : Integrable (fun ω => B ω ^ 3) μ) :
    (∫ ω, (a + B ω) ^ 3 ∂μ) = a ^ 3 + 3 * a ^ 2 * (∫ ω, B ω ∂μ) +
      3 * a * (∫ ω, B ω ^ 2 ∂μ) + ∫ ω, B ω ^ 3 ∂μ := by
  have he : (fun ω => (a + B ω) ^ 3) =
      (fun ω => ((a ^ 3 + 3 * a ^ 2 * B ω) + 3 * a * B ω ^ 2) + B ω ^ 3) := by
    funext ω
    ring
  have hI1 : Integrable (fun ω => a ^ 3 + 3 * a ^ 2 * B ω) μ :=
    (integrable_const _).add (hB.const_mul (3 * a ^ 2))
  have hI2 : Integrable (fun ω => (a ^ 3 + 3 * a ^ 2 * B ω) + 3 * a * B ω ^ 2) μ :=
    hI1.add (hB2.const_mul (3 * a))
  rw [he,
    integral_add (f := fun ω => (a ^ 3 + 3 * a ^ 2 * B ω) + 3 * a * B ω ^ 2)
      (g := fun ω => B ω ^ 3) hI2 hB3,
    integral_add (f := fun ω => a ^ 3 + 3 * a ^ 2 * B ω) (g := fun ω => 3 * a * B ω ^ 2)
      hI1 (hB2.const_mul (3 * a)),
    integral_add (f := fun _ : Ω => a ^ 3) (g := fun ω => 3 * a ^ 2 * B ω)
      (integrable_const _) (hB.const_mul (3 * a ^ 2)),
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]

end ProphetSecretary.Statistics
