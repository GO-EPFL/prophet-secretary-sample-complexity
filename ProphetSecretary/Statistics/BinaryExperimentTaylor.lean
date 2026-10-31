import ProphetSecretary.Probability.BinaryExperiment
import ProphetSecretary.Statistics.BinaryExperimentGap

/-!
# Taylor expansion in the hidden-sign experiment

Payoff functions depend on observed data, never on the hidden sign. The two
hypotheses supply different online laws and analytical targets. Posterior
averaging and four uniform fixed-policy Taylor estimates give the conditional
linearized gap used in `thm:bayes`.
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal

namespace ProphetSecretary.Statistics

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def binaryConditionalPayoff (μ ν : Measure Ω) (fplus fminus : Ω → ℝ) (d : Ω) : ℝ :=
  ((1 + ProphetSecretary.Probability.binaryPosterior μ ν d) / 2) * fplus d +
    ((1 - ProphetSecretary.Probability.binaryPosterior μ ν d) / 2) * fminus d

lemma integrable_mixture {μ ν : Measure Ω} {f : Ω → ℝ}
    (hμ : Integrable f μ) (hν : Integrable f ν) : Integrable f (ProphetSecretary.Probability.binaryMixture μ ν) :=
  hμ.smul_measure_nnreal.add_measure hν.smul_measure_nnreal

lemma integrable_binaryConditionalPayoff (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {fplus fminus : Ω → ℝ}
    (hpμ : Integrable fplus μ) (hpν : Integrable fplus ν)
    (hmμ : Integrable fminus μ) (hmν : Integrable fminus ν) :
    Integrable (binaryConditionalPayoff μ ν fplus fminus) (ProphetSecretary.Probability.binaryMixture μ ν) := by
  have hp := integrable_mixture hpμ hpν
  have hm := integrable_mixture hmμ hmν
  have hZ := (hp.sub hm).mul_bdd (ProphetSecretary.Probability.measurable_binaryPosterior μ ν).aestronglyMeasurable
    (Eventually.of_forall fun d => by
      simpa only [Real.norm_eq_abs] using ProphetSecretary.Probability.binaryPosterior_abs_le_one μ ν d)
  apply (((hp.add hm).const_mul (1 / 2 : ℝ)).add (hZ.const_mul (1 / 2 : ℝ))).congr
  exact Eventually.of_forall fun d => by
    change (1 / 2 : ℝ) * (fplus d + fminus d) +
      (1 / 2 : ℝ) * ((fplus d - fminus d) * ProphetSecretary.Probability.binaryPosterior μ ν d) = _
    unfold binaryConditionalPayoff
    ring

/-- The explicit conditional payoff integrates to the genuine two-hypothesis
experiment, with the same data-dependent functions under the two laws. -/
theorem integral_binaryConditionalPayoff {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) {fplus fminus : Ω → ℝ}
    (hpμ : Integrable fplus μ) (hpν : Integrable fplus ν)
    (hmμ : Integrable fminus μ) (hmν : Integrable fminus ν) :
    (∫ d, binaryConditionalPayoff μ ν fplus fminus d ∂ProphetSecretary.Probability.binaryMixture μ ν) =
      (1 / 2 : ℝ) * (∫ d, fplus d ∂μ) + (1 / 2 : ℝ) * ∫ d, fminus d ∂ν := by
  let D := ProphetSecretary.Probability.binaryMixture μ ν
  let Z := ProphetSecretary.Probability.binaryPosterior μ ν
  let a : Ω → ℝ := fun d => (fplus d + fminus d) / 2
  let b : Ω → ℝ := fun d => (fplus d - fminus d) / 2
  have haμ : Integrable a μ := (hpμ.add hmμ).div_const 2
  have haν : Integrable a ν := (hpν.add hmν).div_const 2
  have hbμ : Integrable b μ := (hpμ.sub hmμ).div_const 2
  have hbν : Integrable b ν := (hpν.sub hmν).div_const 2
  have haD := integrable_mixture haμ haν
  have hbD := integrable_mixture hbμ hbν
  have hZb : Integrable (fun d => Z d * b d) D := by
    have h := hbD.mul_bdd (ProphetSecretary.Probability.measurable_binaryPosterior μ ν).aestronglyMeasurable
      (Eventually.of_forall fun d => by
        simpa only [Real.norm_eq_abs] using ProphetSecretary.Probability.binaryPosterior_abs_le_one μ ν d)
    simpa only [mul_comm] using h
  have heq : (∫ d, binaryConditionalPayoff μ ν fplus fminus d ∂D) =
      (∫ d, a d ∂D) + ∫ d, Z d * b d ∂D := by
    rw [← integral_add haD hZb]
    apply integral_congr_ae
    exact Eventually.of_forall fun d => by dsimp [binaryConditionalPayoff, a, b, Z]; ring
  rw [heq, ProphetSecretary.Probability.integral_binaryMixture haμ haν,
    ProphetSecretary.Probability.binaryPosterior_testing hμν hbμ hbν]
  dsimp [a, b]
  rw [integral_div, integral_div, integral_div, integral_div,
    integral_add hpμ hmμ, integral_add hpν hmν, integral_sub hpμ hmμ, integral_sub hpν hmν]
  ring

lemma combination_taylor_error {A B A₀ B₀ DA DB θ v E : ℝ}
    (hA : |A - A₀ - θ * DA| ≤ E) (hB : |B - B₀ - θ * DB| ≤ E) :
    |(A + v * B) - (A₀ + v * B₀ + θ * (DA + v * DB))| ≤ (1 + |v|) * E := by
  have heq : (A + v * B) - (A₀ + v * B₀ + θ * (DA + v * DB)) =
      (A - A₀ - θ * DA) + v * (B - B₀ - θ * DB) := by ring
  rw [heq]
  calc
    _ ≤ |A - A₀ - θ * DA| + |v * (B - B₀ - θ * DB)| := abs_add_le _ _
    _ = |A - A₀ - θ * DA| + |v| * |B - B₀ - θ * DB| := by rw [abs_mul]
    _ ≤ E + |v| * E := add_le_add hA (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
    _ = _ := by ring

lemma convex_combination_error {a b f g u v E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = 1)
    (hf : |f - u| ≤ E) (hg : |g - v| ≤ E) :
    |(a * f + b * g) - (a * u + b * v)| ≤ E := by
  have heq : (a * f + b * g) - (a * u + b * v) = a * (f - u) + b * (g - v) := by ring
  rw [heq]
  calc
    _ ≤ |a * (f - u)| + |b * (g - v)| := abs_add_le _ _
    _ = a * |f - u| + b * |g - v| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * E + b * E := add_le_add (mul_le_mul_of_nonneg_left hf ha) (mul_le_mul_of_nonneg_left hg hb)
    _ = E := by rw [← add_mul, hsum, one_mul]

/-- Uniform fixed-policy Taylor errors remain uniform after posterior averaging.
The base weight perturbation v is hidden from the data-selected policy. -/
theorem binary_taylor_error {z v t Ap Am Bp Bm A₀ B₀ DA DB E : ℝ}
    (hz : |z| ≤ 1) (hv : 0 ≤ v)
    (hAp : |Ap - A₀ - t * DA| ≤ E) (hAm : |Am - A₀ + t * DA| ≤ E)
    (hBp : |Bp - B₀ - t * DB| ≤ E) (hBm : |Bm - B₀ + t * DB| ≤ E) :
    |((1 + z) / 2) * (Ap + v * Bp) + ((1 - z) / 2) * (Am - v * Bm) -
      (A₀ + v * z * B₀ + t * z * DA + v * t * DB)| ≤ (1 + v) * E := by
  have hp := combination_taylor_error (v := v) hAp hBp
  have hm := combination_taylor_error (θ := -t) (v := -v)
    (by simpa only [neg_mul, sub_neg_eq_add] using hAm)
    (by simpa only [neg_mul, sub_neg_eq_add] using hBm)
  rw [abs_of_nonneg hv] at hp
  rw [abs_neg, abs_of_nonneg hv] at hm
  have hz' := abs_le.mp hz
  have h := convex_combination_error (a := (1 + z) / 2) (b := (1 - z) / 2)
    (by linarith : 0 ≤ (1 + z) / 2) (by linarith : 0 ≤ (1 - z) / 2) (by ring) hp hm
  convert h using 1
  congr 1
  ring

/-- Averaged two-law experiment bound, with the Taylor identification discharged.
The functions are data-dependent fixed-policy payoffs and responses. Instantiating
them with a learner and choosing the asymptotic scales are separate steps. -/
theorem binary_experiment_gap_of_taylor (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ω : ℝ → ℝ) {δ K v b B t I C S₀ DA₀ DB₀ : ℝ}
    (hv : 0 ≤ v) (hB : 0 ≤ B) (ht : 0 ≤ t) (hI : 0 ≤ I)
    (hmono : Monotone ω) (hbound : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B)
    (hInfo : klDiv μ ν + klDiv ν μ ≤ ENNReal.ofReal I)
    (Ap Am Bp Bm A₀ B₀ DA DB r : Ω → ℝ)
    (hpμ : Integrable (fun d => Ap d + v * Bp d) μ)
    (hpν : Integrable (fun d => Ap d + v * Bp d) ν)
    (hmμ : Integrable (fun d => Am d - v * Bm d) μ)
    (hmν : Integrable (fun d => Am d - v * Bm d) ν)
    (hr : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, 0 ≤ r d)
    (hbase : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, A₀ d = δ - r d)
    (hAp : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, |Ap d - A₀ d - t * DA d| ≤ C * t ^ 2)
    (hAm : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, |Am d - A₀ d + t * DA d| ≤ C * t ^ 2)
    (hBp : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, |Bp d - B₀ d - t * DB d| ≤ C * t ^ 2)
    (hBm : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, |Bm d - B₀ d + t * DB d| ≤ C * t ^ 2)
    (hSlope : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν, |B₀ d - S₀| ≤ K * Real.sqrt (r d))
    (hDerivative : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν,
      |DA d - DA₀| + |DB d - DB₀| ≤ ω (r d)) (hDB₀ : DB₀ ≤ -b) :
    (1 / 2 : ℝ) * (∫ d, Ap d + v * Bp d ∂μ) + (1 / 2 : ℝ) * (∫ d, Am d - v * Bm d ∂ν) ≤
      δ - v * b * t + ((K * v) ^ 2 / 8) * I + bayesModulusError ω (1 + v) B t +
        (1 + v) * C * t ^ 2 := by
  let G := binaryConditionalPayoff μ ν (fun d => Ap d + v * Bp d) (fun d => Am d - v * Bm d)
  have hG := integrable_binaryConditionalPayoff μ ν hpμ hpν hmμ hmν
  have hGap : ∀ᵐ d ∂ProphetSecretary.Probability.binaryMixture μ ν,
      G d ≤ δ - r d + v * ProphetSecretary.Probability.binaryPosterior μ ν d * B₀ d +
        t * ProphetSecretary.Probability.binaryPosterior μ ν d * DA d + v * t * DB d +
          (1 + v) * C * t ^ 2 := by
    filter_upwards [hbase, hAp, hAm, hBp, hBm] with d hd hpa hma hpb hmb
    have h := binary_taylor_error (ProphetSecretary.Probability.binaryPosterior_abs_le_one μ ν d)
      hv hpa hma hpb hmb
    have hu := (abs_le.mp h).2
    change G d - (A₀ d + v * ProphetSecretary.Probability.binaryPosterior μ ν d * B₀ d +
      t * ProphetSecretary.Probability.binaryPosterior μ ν d * DA d + v * t * DB d) ≤ _ at hu
    rw [hd] at hu
    nlinarith
  have hstat := binary_expected_gap_le μ ν ω hv hB ht hI hmono hbound hInfo
    G r B₀ DA DB hG hr hGap hSlope hDerivative hDB₀
  have hsum : klDiv μ ν + klDiv ν μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hInfo
  have hμν : μ ≪ ν := (klDiv_ne_top_iff.mp (ENNReal.add_ne_top.mp hsum).1).1
  rw [← integral_binaryConditionalPayoff hμν hpμ hpν hmμ hmν]
  exact hstat

end ProphetSecretary.Statistics
