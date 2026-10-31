import ProphetSecretary.Statistics.BinaryRegretAbsorption
import ProphetSecretary.Probability.BinaryPosterior

/-!
# Averaging the regret bound in the binary experiment

The hypotheses below concern the displayed linearized conditional gap. The
Taylor expansion and its identification with an actual learner payoff are
separate obligations in the statistical experiment. All information and modulus
constants are explicit; the posterior is the constructed binary posterior.
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal

namespace ProphetSecretary.Statistics

lemma centered_bayes_gap_bound (ω : ℝ → ℝ) {δ r z K v b B t S S₀ DA DA₀ DB DB₀ : ℝ}
    (hr : 0 ≤ r) (hv : 0 ≤ v) (hB : 0 ≤ B) (ht : 0 ≤ t) (hz : |z| ≤ 1)
    (hmono : Monotone ω) (hbound : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B)
    (hSlope : |S - S₀| ≤ K * Real.sqrt r)
    (hDerivative : |DA - DA₀| + |DB - DB₀| ≤ ω r) (hDB₀ : DB₀ ≤ -b) :
    δ - r + v * z * S + t * z * DA + v * t * DB ≤
      v * z * S₀ + t * z * DA₀ + δ - v * b * t +
        ((K * v) ^ 2 / 2) * z ^ 2 + bayesModulusError ω (1 + v) B t := by
  have hS : v * (z * (S - S₀)) ≤ K * v * |z| * Real.sqrt r := by
    have h : z * (S - S₀) ≤ |z| * (K * Real.sqrt r) := by
      calc
        _ ≤ |z * (S - S₀)| := le_abs_self _
        _ = |z| * |S - S₀| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hSlope (abs_nonneg _)
    have hm := mul_le_mul_of_nonneg_left h hv
    nlinarith
  have hA : t * (z * (DA - DA₀)) ≤ t * |DA - DA₀| := by
    apply mul_le_mul_of_nonneg_left _ ht
    calc
      _ ≤ |z * (DA - DA₀)| := le_abs_self _
      _ = |z| * |DA - DA₀| := abs_mul _ _
      _ ≤ 1 * |DA - DA₀| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      _ = _ := one_mul _
  have hD : v * t * DB ≤ -v * b * t + v * t * |DB - DB₀| := by
    have hdb : DB ≤ -b + |DB - DB₀| := by linarith [le_abs_self (DB - DB₀)]
    have hm := mul_le_mul_of_nonneg_left hdb (mul_nonneg hv ht)
    nlinarith
  have hE : t * |DA - DA₀| + v * t * |DB - DB₀| ≤ (1 + v) * t * ω r := by
    have hm := mul_le_mul_of_nonneg_left hDerivative (mul_nonneg (by linarith : 0 ≤ 1 + v) ht)
    have h₁ := mul_nonneg (mul_nonneg hv ht) (abs_nonneg (DA - DA₀))
    have h₂ := mul_nonneg ht (abs_nonneg (DB - DB₀))
    nlinarith
  have hCore := bayes_regret_absorption (δ := δ) (z := z) (K := K) (b := b) (C := 0)
    ω hr hv hB ht hmono hbound
  simp only [zero_mul, add_zero] at hCore
  nlinarith

/-- Explicit information bound for the averaged linearized experiment. The mean
posterior terms at the fixed base optimizer vanish exactly. -/
theorem binary_expected_gap_le {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ω : ℝ → ℝ) {δ K v b B t I E S₀ DA₀ DB₀ : ℝ}
    (hv : 0 ≤ v) (hB : 0 ≤ B) (ht : 0 ≤ t) (hI : 0 ≤ I)
    (hmono : Monotone ω) (hbound : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B)
    (hInfo : klDiv μ ν + klDiv ν μ ≤ ENNReal.ofReal I)
    (G r S DA DB : Ω → ℝ) (hG : Integrable G (ProphetSecretary.Probability.binaryMixture μ ν))
    (hr : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, 0 ≤ r d)
    (hGap : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν,
      G d ≤ δ - r d + v * ProphetSecretary.Probability.binaryPosterior μ ν d * S d +
        t * ProphetSecretary.Probability.binaryPosterior μ ν d * DA d + v * t * DB d + E)
    (hSlope : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, |S d - S₀| ≤ K * Real.sqrt (r d))
    (hDerivative : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν,
      |DA d - DA₀| + |DB d - DB₀| ≤ ω (r d)) (hDB₀ : DB₀ ≤ -b) :
    (∫ d, G d ∂ProphetSecretary.Probability.binaryMixture μ ν) ≤
      δ - v * b * t + ((K * v) ^ 2 / 8) * I + bayesModulusError ω (1 + v) B t + E := by
  let D := ProphetSecretary.Probability.binaryMixture μ ν
  let Z := ProphetSecretary.Probability.binaryPosterior μ ν
  let C := δ - v * b * t + bayesModulusError ω (1 + v) B t + E
  let F : Ω → ℝ := fun d => C + ((K * v) ^ 2 / 2) * Z d ^ 2 +
    (v * S₀ + t * DA₀) * Z d
  have hZ : Integrable Z D := ProphetSecretary.Probability.binaryPosterior_integrable μ ν D
  have hZ₂ : Integrable (fun d => Z d ^ 2) D := ProphetSecretary.Probability.binaryPosterior_sq_integrable μ ν D
  have hF : Integrable F D :=
    ((integrable_const C).add (hZ₂.const_mul ((K * v) ^ 2 / 2))).add
      (hZ.const_mul (v * S₀ + t * DA₀))
  have hpoint : ∀ᵐ d ∂D, G d ≤ F d := by
    filter_upwards [hr, hGap, hSlope, hDerivative] with d hdr hdg hds hdd
    have h := centered_bayes_gap_bound (δ := δ) ω hdr hv hB ht
      (ProphetSecretary.Probability.binaryPosterior_abs_le_one μ ν d) hmono hbound hds hdd hDB₀
    dsimp [F, C, Z]
    nlinarith
  have hsum : klDiv μ ν + klDiv ν μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hInfo
  have hμν : μ ≪ ν := (klDiv_ne_top_iff.mp (ENNReal.add_ne_top.mp hsum).1).1
  have hmean := ProphetSecretary.Probability.binaryPosterior_mean_zero hμν
  have hvar := ProphetSecretary.Probability.binaryPosterior_secondMoment_le_information hI hInfo
  have hint : (∫ d, F d ∂D) = C + ((K * v) ^ 2 / 2) * (∫ d, Z d ^ 2 ∂D) := by
    dsimp [F]
    rw [integral_add (μ := D) (f := fun d => C + ((K * v) ^ 2 / 2) * Z d ^ 2)
      (g := fun d => (v * S₀ + t * DA₀) * Z d)
      ((integrable_const C).add (hZ₂.const_mul _)) (hZ.const_mul _),
      integral_add (μ := D) (f := fun _ => C) (g := fun d => ((K * v) ^ 2 / 2) * Z d ^ 2)
        (integrable_const C) (hZ₂.const_mul _), integral_const_mul, integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    change C + ((K * v) ^ 2 / 2) * (∫ d, Z d ^ 2 ∂D) +
      (v * S₀ + t * DA₀) * (∫ d, Z d ∂D) = _
    rw [hmean, mul_zero, add_zero]
  have hcoeff := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ (K * v) ^ 2 / 2)
  have h := (integral_mono_ae hG hF hpoint).trans_eq hint
  dsimp [C, Z, D] at h hcoeff
  nlinarith

end ProphetSecretary.Statistics
