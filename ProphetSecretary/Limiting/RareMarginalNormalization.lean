import ProphetSecretary.Limiting.RareMarginal
import ProphetSecretary.Limiting.BernoulliPotential

/-!
# Identifying the continuous rare marginal with a Bernoulli mark law

The finite law is exactly a zero-inflated normalized mark distribution.
Normalization is used only in this equality and the existing quantitative
Poisson comparison; weak convergence is proved for the unnormalized finite
mixture, including when the limiting intensity is zero.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

noncomputable def rareParameter (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) : unitInterval :=
  ⟨((q⁻¹*μ.mass : ℝ≥0) : ℝ),NNReal.coe_nonneg _,by
    have hfrac : q⁻¹*μ.mass ≤ 1 := by
      simpa only [div_eq_mul_inv,mul_comm] using (div_le_one hq).mpr hm
    exact_mod_cast hfrac⟩

lemma rareParameter_toNNReal (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    unitInterval.toNNReal (rareParameter μ q hq hm) = q⁻¹*μ.mass := by
  apply Subtype.ext
  rfl
lemma rareParameter_symm_toNNReal (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    unitInterval.toNNReal (unitInterval.symm (rareParameter μ q hq hm)) = 1-q⁻¹*μ.mass := by
  have hfrac : q⁻¹*μ.mass ≤ 1 := by
    simpa only [div_eq_mul_inv,mul_comm] using (div_le_one hq).mpr hm
  apply Subtype.ext
  change (1 : ℝ)-((q⁻¹*μ.mass : ℝ≥0) : ℝ) = ((1-q⁻¹*μ.mass : ℝ≥0) : ℝ)
  rw [NNReal.coe_sub hfrac]
  norm_num

lemma normalizedMarkOrZero_mass_smul (μ : FiniteMeasure ℝ) :
    μ.mass • normalizedMarkOrZero μ = (μ : Measure ℝ) := by
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [normalizedMarkOrZero,if_neg hμ]
    exact (congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize).symm

lemma rareProbabilityLaw_eq_zeroInflated (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    (rareProbabilityLaw μ q hq hm : Measure ℝ) = zeroInflatedLaw (normalizedMarkOrZero μ) (rareParameter μ q hq hm) := by
  have hp2 : unitInterval.toNNReal (unitInterval.symm (unitInterval.symm (rareParameter μ q hq hm))) = q⁻¹*μ.mass := by
    apply Subtype.ext
    change (1 : ℝ)-(1-((q⁻¹*μ.mass : ℝ≥0) : ℝ)) = ((q⁻¹*μ.mass : ℝ≥0) : ℝ)
    ring
  change (rareFiniteLaw μ q : Measure ℝ) = _
  rw [rareFiniteLaw,FiniteMeasure.toMeasure_add,FiniteMeasure.toMeasure_smul,FiniteMeasure.toMeasure_smul]
  change (1-q⁻¹*μ.mass) • Measure.dirac 0 + q⁻¹ • (μ : Measure ℝ) = _
  rw [← normalizedMarkOrZero_mass_smul μ,smul_smul,zeroInflatedLaw,Model.jackpotLaw,
    rareParameter_symm_toNNReal,hp2]

lemma rareProbabilityLaw_bounds (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hsupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    ∀ᵐ x ∂(rareProbabilityLaw μ q hq hm : Measure ℝ), x ∈ Icc (0 : ℝ) H := by
  change ∀ᵐ x ∂((1-q⁻¹*μ.mass) • Measure.dirac 0 + q⁻¹ • (μ : Measure ℝ)), x ∈ Icc (0 : ℝ) H
  rw [ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (by simp [H.coe_nonneg]) _,Measure.ae_smul_measure hsupp _⟩

lemma rareParameter_total (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    (μ : Measure ℝ).real univ = (q : ℝ)*(rareParameter μ q hq hm : ℝ) := by
  change (μ.mass : ℝ) = (q : ℝ)*((q⁻¹*μ.mass : ℝ≥0) : ℝ)
  rw [NNReal.coe_mul,NNReal.coe_inv]
  have hqR : (q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
  field_simp

lemma integrable_rareProbabilityLaw (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q)
    {f : ℝ → ℝ} (hf : Integrable f (μ : Measure ℝ)) : Integrable f (rareProbabilityLaw μ q hq hm : Measure ℝ) := by
  change Integrable f ((1-q⁻¹*μ.mass) • Measure.dirac 0+q⁻¹ • (μ : Measure ℝ))
  exact ((integrable_dirac (by simp) : Integrable f (Measure.dirac (0 : ℝ))).smul_measure_nnreal).add_measure
    hf.smul_measure_nnreal

lemma integral_rareProbabilityLaw (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q)
    (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(rareProbabilityLaw μ q hq hm : Measure ℝ)) =
      f 0+(q : ℝ)⁻¹*((∫ x, f x ∂(μ : Measure ℝ))-(μ.mass : ℝ)*f 0) := by
  rw [rareProbabilityLaw_eq_zeroInflated,integral_zeroInflatedLaw _ _ (f.integrable (normalizedMarkOrZero μ))]
  have hM : (μ.mass : ℝ)*(∫ x, f x ∂normalizedMarkOrZero μ) = ∫ x, f x ∂(μ : Measure ℝ) := by
    rw [← normalizedMarkOrZero_mass_smul μ,integral_smul_nnreal_measure]
    rfl
  change (1-((q⁻¹*μ.mass : ℝ≥0) : ℝ))*f 0+((q⁻¹*μ.mass : ℝ≥0) : ℝ)*(∫ x, f x ∂normalizedMarkOrZero μ) = _
  rw [NNReal.coe_mul,NNReal.coe_inv]
  calc
    _ = f 0+(q : ℝ)⁻¹*((μ.mass : ℝ)*(∫ x, f x ∂normalizedMarkOrZero μ)-(μ.mass : ℝ)*f 0) := by ring
    _ = _ := by rw [hM]

end ProphetSecretary.Limiting
