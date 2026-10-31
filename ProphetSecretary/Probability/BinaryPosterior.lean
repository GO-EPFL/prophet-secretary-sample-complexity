import ProphetSecretary.Probability.LikelihoodInformation
import ProphetSecretary.Analysis.SymmetricLog

/-!
# The posterior sign in a binary statistical experiment

The observation law is the equal mixture of the two hypotheses. The posterior
sign is constructed from the actual Radon--Nikodym likelihood ratio. Its testing
identity, zero mean, and second moment are derived, not postulated as properties
of a posterior interface. Paper correspondence: `thm:bayes`.
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def binaryMixture (μ ν : Measure Ω) : Measure Ω :=
  (1 / 2 : NNReal) • μ + (1 / 2 : NNReal) • ν

instance binaryMixture_probability (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (binaryMixture μ ν) := by
  constructor
  norm_num [binaryMixture, ENNReal.inv_two_add_inv_two]

noncomputable def binaryLikelihoodRatio (μ ν : Measure Ω) (x : Ω) : ℝ :=
  (μ.rnDeriv ν x).toReal

noncomputable def binaryPosterior (μ ν : Measure Ω) (x : Ω) : ℝ :=
  (binaryLikelihoodRatio μ ν x - 1) / (binaryLikelihoodRatio μ ν x + 1)

lemma integral_binaryLikelihoodRatio_mul {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) (f : Ω → ℝ) :
    (∫ x, binaryLikelihoodRatio μ ν x * f x ∂ν) = ∫ x, f x ∂μ :=
  integral_toReal_rnDeriv_mul hμν

lemma measurable_binaryPosterior (μ ν : Measure Ω) : Measurable (binaryPosterior μ ν) :=
  (((Measure.measurable_rnDeriv μ ν).ennreal_toReal).sub measurable_const).div
    (((Measure.measurable_rnDeriv μ ν).ennreal_toReal).add measurable_const)

lemma binaryPosterior_abs_le_one (μ ν : Measure Ω) (x : Ω) : |binaryPosterior μ ν x| ≤ 1 := by
  have hr : 0 ≤ binaryLikelihoodRatio μ ν x := ENNReal.toReal_nonneg
  rw [binaryPosterior, abs_div, abs_of_pos (by positivity : 0 < binaryLikelihoodRatio μ ν x + 1)]
  apply (div_le_one (by positivity : 0 < binaryLikelihoodRatio μ ν x + 1)).mpr
  rw [abs_le]
  constructor <;> linarith

lemma binaryPosterior_integrable (μ ν ρ : Measure Ω) [IsFiniteMeasure ρ] :
    Integrable (binaryPosterior μ ν) ρ := by
  apply Integrable.of_bound (measurable_binaryPosterior μ ν).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using binaryPosterior_abs_le_one μ ν x

lemma binaryPosterior_sq_integrable (μ ν ρ : Measure Ω) [IsFiniteMeasure ρ] :
    Integrable (fun x => binaryPosterior μ ν x ^ 2) ρ := by
  apply Integrable.of_bound ((measurable_binaryPosterior μ ν).pow_const 2).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (binaryPosterior_abs_le_one μ ν x)

lemma integral_binaryMixture {μ ν : Measure Ω} {f : Ω → ℝ}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    (∫ x, f x ∂binaryMixture μ ν) = (1 / 2 : ℝ) * (∫ x, f x ∂μ) +
      (1 / 2 : ℝ) * (∫ x, f x ∂ν) := by
  rw [binaryMixture, integral_add_measure hμ.smul_measure_nnreal hν.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  rfl

lemma integral_binaryMixture_density {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) {f : Ω → ℝ}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    (∫ x, f x ∂binaryMixture μ ν) = (1 / 2 : ℝ) *
      ∫ x, (binaryLikelihoodRatio μ ν x + 1) * f x ∂ν := by
  have hrf : Integrable (fun x => binaryLikelihoodRatio μ ν x * f x) ν :=
    (integrable_toReal_rnDeriv_mul_iff hμν).mpr hμ
  have hsum : (∫ x, (binaryLikelihoodRatio μ ν x + 1) * f x ∂ν) =
      (∫ x, binaryLikelihoodRatio μ ν x * f x ∂ν) + ∫ x, f x ∂ν := by
    rw [← integral_add hrf hν]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [integral_binaryMixture hμ hν, hsum, integral_binaryLikelihoodRatio_mul hμν]
  ring

/-- Testing identity characterizing the conditional mean of a uniform hidden sign.
The observation statistic may be arbitrary integrable data-dependent information. -/
theorem binaryPosterior_testing {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) {f : Ω → ℝ}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    (∫ x, binaryPosterior μ ν x * f x ∂binaryMixture μ ν) =
      (1 / 2 : ℝ) * ((∫ x, f x ∂μ) - ∫ x, f x ∂ν) := by
  have hprod (ρ : Measure Ω) (hρ : Integrable f ρ) :
      Integrable (fun x => binaryPosterior μ ν x * f x) ρ := by
    have h := hρ.mul_bdd (measurable_binaryPosterior μ ν).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using binaryPosterior_abs_le_one μ ν x)
    simpa only [mul_comm] using h
  rw [integral_binaryMixture_density hμν (hprod μ hμ) (hprod ν hν)]
  have hrf : Integrable (fun x => binaryLikelihoodRatio μ ν x * f x) ν :=
    (integrable_toReal_rnDeriv_mul_iff hμν).mpr hμ
  have heq : (∫ x, (binaryLikelihoodRatio μ ν x + 1) * (binaryPosterior μ ν x * f x) ∂ν) =
      (∫ x, binaryLikelihoodRatio μ ν x * f x ∂ν) - ∫ x, f x ∂ν := by
    rw [← integral_sub hrf hν]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hpos : 0 < binaryLikelihoodRatio μ ν x + 1 := by
        have h : 0 ≤ binaryLikelihoodRatio μ ν x := ENNReal.toReal_nonneg
        positivity
      dsimp [binaryPosterior]
      field_simp [ne_of_gt hpos]
  rw [heq, integral_binaryLikelihoodRatio_mul hμν]

theorem binaryPosterior_mean_zero {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    (∫ x, binaryPosterior μ ν x ∂binaryMixture μ ν) = 0 := by
  simpa using binaryPosterior_testing hμν (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))

theorem binaryPosterior_secondMoment_eq {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    (∫ x, binaryPosterior μ ν x ^ 2 ∂binaryMixture μ ν) = (1 / 2 : ℝ) *
      ∫ x, (binaryLikelihoodRatio μ ν x - 1) ^ 2 / (binaryLikelihoodRatio μ ν x + 1) ∂ν := by
  rw [integral_binaryMixture_density hμν (binaryPosterior_sq_integrable μ ν μ)
    (binaryPosterior_sq_integrable μ ν ν)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have hpos : 0 < binaryLikelihoodRatio μ ν x + 1 := by
      have h : 0 ≤ binaryLikelihoodRatio μ ν x := ENNReal.toReal_nonneg
      positivity
    dsimp [binaryPosterior]
    field_simp [ne_of_gt hpos]

noncomputable def binaryTriangular (μ ν : Measure Ω) (x : Ω) : ℝ :=
  (binaryLikelihoodRatio μ ν x - 1) ^ 2 / (binaryLikelihoodRatio μ ν x + 1)

lemma binaryTriangular_nonnegative (μ ν : Measure Ω) (x : Ω) : 0 ≤ binaryTriangular μ ν x := by
  have hr : 0 ≤ binaryLikelihoodRatio μ ν x := ENNReal.toReal_nonneg
  exact div_nonneg (sq_nonneg _) (by positivity)

lemma binaryTriangular_integrable {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) : Integrable (binaryTriangular μ ν) ν := by
  have hrInt : Integrable (binaryLikelihoodRatio μ ν) ν := by
    change Integrable (fun x => (μ.rnDeriv ν x).toReal) ν
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hμν).mpr (integrable_const (1 : ℝ))
  have hrMeas : Measurable (binaryLikelihoodRatio μ ν) := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  apply (hrInt.add (integrable_const 1)).mono'
    (((hrMeas.sub measurable_const).pow_const 2).div (hrMeas.add measurable_const)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖binaryTriangular μ ν x‖ ≤ binaryLikelihoodRatio μ ν x + 1
  rw [Real.norm_eq_abs, abs_of_nonneg (binaryTriangular_nonnegative μ ν x)]
  have hr : 0 ≤ binaryLikelihoodRatio μ ν x := ENNReal.toReal_nonneg
  apply (div_le_iff₀ (by positivity : 0 < binaryLikelihoodRatio μ ν x + 1)).mpr
  nlinarith

/-- The posterior sign's second moment is bounded by one quarter of symmetric KL.
Finiteness of the divergences supplies absolute continuity and all log integrability. -/
theorem binaryPosterior_secondMoment_le_symmetricKL {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hKL₁ : klDiv μ ν ≠ ∞) (hKL₂ : klDiv ν μ ≠ ∞) :
    (∫ x, binaryPosterior μ ν x ^ 2 ∂binaryMixture μ ν) ≤
      ((klDiv μ ν).toReal + (klDiv ν μ).toReal) / 4 := by
  obtain ⟨hμν, hlogμ⟩ := klDiv_ne_top_iff.mp hKL₁
  obtain ⟨hνμ, hlogν'⟩ := klDiv_ne_top_iff.mp hKL₂
  have hlogν : Integrable (fun x => Real.log (binaryLikelihoodRatio μ ν x)) ν :=
    hlogν'.neg.congr (neg_llr hνμ)
  have hrlog : Integrable (fun x => binaryLikelihoodRatio μ ν x *
      Real.log (binaryLikelihoodRatio μ ν x)) ν :=
    (integrable_toReal_rnDeriv_mul_iff hμν).mpr hlogμ
  have hcostInt : Integrable (fun x => (binaryLikelihoodRatio μ ν x - 1) *
      Real.log (binaryLikelihoodRatio μ ν x)) ν := by
    apply (hrlog.sub hlogν).congr
    exact Eventually.of_forall fun x => by
      change binaryLikelihoodRatio μ ν x * Real.log (binaryLikelihoodRatio μ ν x) -
        Real.log (binaryLikelihoodRatio μ ν x) =
          (binaryLikelihoodRatio μ ν x - 1) * Real.log (binaryLikelihoodRatio μ ν x)
      ring
  have hKL₁eq : (klDiv μ ν).toReal =
      ∫ x, binaryLikelihoodRatio μ ν x * Real.log (binaryLikelihoodRatio μ ν x) ∂ν := by
    rw [toReal_klDiv_of_measure_eq hμν (by simp)]
    exact (integral_binaryLikelihoodRatio_mul hμν _).symm
  have hKL₂eq : (klDiv ν μ).toReal = -(∫ x, Real.log (binaryLikelihoodRatio μ ν x) ∂ν) := by
    rw [toReal_klDiv_of_measure_eq hνμ (by simp)]
    have hneg : llr ν μ =ᵐ[ν] fun x => -llr μ ν x := by
      filter_upwards [neg_llr hνμ] with x hx
      change -llr ν μ x = llr μ ν x at hx
      linarith
    rw [integral_congr_ae hneg, integral_neg]
    rfl
  have hcosteq : (∫ x, (binaryLikelihoodRatio μ ν x - 1) *
      Real.log (binaryLikelihoodRatio μ ν x) ∂ν) =
        (klDiv μ ν).toReal + (klDiv ν μ).toReal := by
    calc
      _ = (∫ x, binaryLikelihoodRatio μ ν x * Real.log (binaryLikelihoodRatio μ ν x) ∂ν) -
          ∫ x, Real.log (binaryLikelihoodRatio μ ν x) ∂ν := by
        rw [← integral_sub hrlog hlogν]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by rw [hKL₁eq, hKL₂eq]; ring
  have hrpos : ∀ᵐ x ∂ν, 0 < binaryLikelihoodRatio μ ν x := by
    filter_upwards [Measure.rnDeriv_pos' hνμ, Measure.rnDeriv_lt_top μ ν] with x hp ht
    exact ENNReal.toReal_pos hp.ne' ht.ne
  have hdom := integral_mono_ae ((binaryTriangular_integrable hμν).const_mul 2) hcostInt
    (hrpos.mono fun x hx => by
      simpa only [binaryTriangular, mul_div_assoc] using ProphetSecretary.Analysis.symmetricLog_ge_triangular hx)
  rw [integral_const_mul, hcosteq] at hdom
  rw [binaryPosterior_secondMoment_eq hμν]
  change (1 / 2 : ℝ) * (∫ x, binaryTriangular μ ν x ∂ν) ≤ _
  linarith

/-- A finite symmetric information bound directly controls posterior bias. -/
theorem binaryPosterior_secondMoment_le_information {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {I : ℝ} (hI : 0 ≤ I)
    (hInfo : klDiv μ ν + klDiv ν μ ≤ ENNReal.ofReal I) :
    (∫ x, binaryPosterior μ ν x ^ 2 ∂binaryMixture μ ν) ≤ I / 4 := by
  have hsum : klDiv μ ν + klDiv ν μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hInfo
  obtain ⟨hKL₁, hKL₂⟩ := ENNReal.add_ne_top.mp hsum
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hInfo
  rw [ENNReal.toReal_add hKL₁ hKL₂, ENNReal.toReal_ofReal hI] at hreal
  exact (binaryPosterior_secondMoment_le_symmetricKL hKL₁ hKL₂).trans
    (div_le_div_of_nonneg_right hreal (by norm_num))

end ProphetSecretary.Probability
