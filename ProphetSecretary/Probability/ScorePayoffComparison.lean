import ProphetSecretary.Probability.BoundedScorePayoffMoment
import Mathlib.Probability.HasLaw

/-!
# Payoff expectations under square-integrably close analytical scores

The same arbitrary independent auxiliary randomness is retained. The payoff
may depend on the complete main and auxiliary data; its bound, rather than
independence from the scores, controls the expectation error.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace ProphetSecretary.Probability
variable {Ω Aux : Type*} [MeasurableSpace Ω] [MeasurableSpace Aux]

lemma abs_integral_le_sqrt_secondMoment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) {I : ℝ} (hI : (∫ q, (f q)^2 ∂μ)≤I) :
    |∫ q, f q ∂μ|≤Real.sqrt I := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal (2:ℝ)) μ by simpa using hf)
    (show MemLp (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal (2:ℝ)) μ from memLp_const 1)
  have hCS : (∫ q, |f q| ∂μ)≤Real.sqrt (∫ q, (f q)^2 ∂μ) := by
    simpa only [Real.norm_eq_abs,abs_one,mul_one,one_pow,integral_const,probReal_univ,one_smul,
      Real.one_rpow,Real.sqrt_one,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] using h
  exact abs_integral_le_integral_abs.trans (hCS.trans (Real.sqrt_le_sqrt hI))

lemma score_payoff_difference_le_L2 (μ : Measure Ω) (ν : Measure Aux)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s t : Ω → ℝ) (hs : MemLp s 2 μ) (ht : MemLp t 2 μ)
    {I D : ℝ} (hI : (∫ q, (s q-t q)^2 ∂μ)≤I)
    (g : Ω × Aux → ℝ) (hg : Measurable g) (hD : 0≤D) (hb : ∀ q, |g q|≤D) :
    |(∫ q, s q.1*g q ∂μ.prod ν)-(∫ q, t q.1*g q ∂μ.prod ν)|≤Real.sqrt (D^2*I) := by
  have hFst : MeasurePreserving (Prod.fst : Ω × Aux → Ω) (μ.prod ν) μ := measurePreserving_fst
  have hSLp := hs.comp_measurePreserving hFst
  have hTLp := ht.comp_measurePreserving hFst
  have hDiff : MemLp (fun q : Ω × Aux => s q.1-t q.1) 2 (μ.prod ν) := hSLp.sub hTLp
  have hDiffMoment : (∫ q : Ω × Aux, (s q.1-t q.1)^2 ∂μ.prod ν)≤I := by
    have he := hFst.hasLaw.integral_comp ((hs.sub ht).aestronglyMeasurable.pow 2)
    exact he.trans_le hI
  have hMoment := bounded_score_payoff_memLp_and_secondMoment (μ.prod ν)
    (fun q => s q.1-t q.1) g hDiff hg.aestronglyMeasurable hDiffMoment hD (Eventually.of_forall hb)
  have hBound : ∀ᵐ q ∂μ.prod ν, ‖g q‖≤D := Eventually.of_forall (fun q => by
    simpa only [Real.norm_eq_abs] using hb q)
  have hsInt : Integrable (fun q : Ω × Aux => s q.1*g q) (μ.prod ν) := by
    simpa only [Function.comp_def,mul_comm] using (hSLp.integrable (by norm_num : (1:ℝ≥0∞)≤2)).bdd_mul hg.aestronglyMeasurable hBound
  have htInt : Integrable (fun q : Ω × Aux => t q.1*g q) (μ.prod ν) := by
    simpa only [Function.comp_def,mul_comm] using (hTLp.integrable (by norm_num : (1:ℝ≥0∞)≤2)).bdd_mul hg.aestronglyMeasurable hBound
  rw [← integral_sub hsInt htInt]
  have he : (fun q : Ω × Aux => s q.1*g q-t q.1*g q)=
      (fun q => (s q.1-t q.1)*g q) := by funext q; ring
  rw [he]
  exact abs_integral_le_sqrt_secondMoment (μ.prod ν) _ hMoment.1 hMoment.2
end ProphetSecretary.Probability
