import ProphetSecretary.Limiting.ChronologicalPoissonPayload
import ProphetSecretary.Limiting.ZeroIntensity
import ProphetSecretary.Probability.PoissonFiniteSum

/-!
# The actual displayed intensity of independent mark payloads

A finite mark intensity and independent tag law are pushed forward by the
specified display map. Total intensity is unchanged. The normalized display
law and actual Poisson configuration law are identified separately, with the
zero-rate case proved through its empty actual configuration.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

noncomputable def payloadMarkProbability (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ] : ProbabilityMeasure (ℝ × T) :=
  ⟨(μ.normalize : Measure ℝ).prod κ,inferInstance⟩

noncomputable def displayedPayloadMarkLaw (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (g : ℝ × T → ℝ) (hg : Measurable g) : ProbabilityMeasure ℝ :=
  (payloadMarkProbability μ κ).map hg.aemeasurable

noncomputable def displayedPayloadIntensity (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (g : ℝ × T → ℝ) (hg : Measurable g) : FiniteMeasure ℝ :=
  μ.mass • (displayedPayloadMarkLaw μ κ g hg).toFiniteMeasure

lemma displayedPayloadIntensity_mass (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (g : ℝ × T → ℝ) (hg : Measurable g) : (displayedPayloadIntensity μ κ g hg).mass=μ.mass := by
  change (μ.mass • (displayedPayloadMarkLaw μ κ g hg).toFiniteMeasure) univ=μ.mass
  rw [FiniteMeasure.smul_apply]
  change μ.mass*(displayedPayloadMarkLaw μ κ g hg).toFiniteMeasure.mass=μ.mass
  rw [ProbabilityMeasure.mass_toFiniteMeasure,mul_one]

lemma displayedPayloadIntensity_normalize (μ : FiniteMeasure ℝ) (hμ : μ≠0)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g) :
    (displayedPayloadIntensity μ κ g hg).normalize=displayedPayloadMarkLaw μ κ g hg := by
  have hMass : μ.mass≠0 := μ.mass_nonzero_iff.mpr hμ
  have hNew : displayedPayloadIntensity μ κ g hg≠0 := by
    rw [← FiniteMeasure.mass_nonzero_iff,displayedPayloadIntensity_mass]
    exact hMass
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding ℝ).injective
  rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero _ hNew,displayedPayloadIntensity_mass,
    displayedPayloadIntensity,smul_smul,inv_mul_cancel₀ hMass,one_smul]

lemma displayedPayloadIntensity_toMeasure (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (g : ℝ × T → ℝ) (hg : Measurable g) :
    (displayedPayloadIntensity μ κ g hg : Measure ℝ)=((μ : Measure ℝ).prod κ).map g := by
  have hOld : (μ : Measure ℝ)=μ.mass • (μ.normalize : Measure ℝ) := by
    have h := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize
    simpa only [FiniteMeasure.toMeasure_smul,ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using h
  rw [hOld,Measure.prod_smul_left,Measure.map_smul]
  change ((μ.mass • (displayedPayloadMarkLaw μ κ g hg).toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ)=_
  rw [FiniteMeasure.toMeasure_smul]
  rfl

lemma rateConfigurationLaw_zero (p : Measure ℝ) [IsProbabilityMeasure p] :
    rateConfigurationLaw 0 p=Measure.dirac emptyConfiguration := by
  have hCount : MeasurePreserving (fun ω : Configuration => ω.1) (rateConfigurationLaw 0 p) (ProbabilityTheory.poissonMeasure 0) :=
    ⟨measurable_configuration_count,rateConfigurationLaw_count_map 0 p⟩
  have hZero : ∀ᵐ n : ℕ ∂ProbabilityTheory.poissonMeasure 0, n=0 := by
    rw [ProphetSecretary.Probability.poissonMeasure_zero_eq_dirac]
    simp
  have hAE : (id : Configuration → Configuration)=ᵐ[rateConfigurationLaw 0 p] fun _ => emptyConfiguration := by
    filter_upwards [hCount.quasiMeasurePreserving.ae hZero] with ω hω
    rcases ω with ⟨N,pts⟩
    change N=0 at hω
    subst N
    change configurationMk 0 pts=configurationMk 0 (fun j => Fin.elim0 j)
    congr 1
    funext j
    exact Fin.elim0 j
  calc
    _ = (rateConfigurationLaw 0 p).map id := by rw [Measure.map_id]
    _ = (rateConfigurationLaw 0 p).map (fun _ => emptyConfiguration) := Measure.map_congr hAE
    _ = _ := by rw [Measure.map_const,measure_univ,one_smul]

lemma configurationLaw_displayedPayloadIntensity (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (g : ℝ × T → ℝ) (hg : Measurable g) :
    configurationLaw (displayedPayloadIntensity μ κ g hg)=
      rateConfigurationLaw μ.mass (displayedPayloadMarkLaw μ κ g hg : Measure ℝ) := by
  by_cases hμ : μ=0
  · subst μ
    have hMass0 : (0 : FiniteMeasure ℝ).mass=0 := (FiniteMeasure.mass_zero_iff _).mpr rfl
    simp only [displayedPayloadIntensity,hMass0,zero_smul,configurationLaw_zero,rateConfigurationLaw_zero]
  · rw [← rateConfigurationLaw_actual,displayedPayloadIntensity_mass,displayedPayloadIntensity_normalize μ hμ]

end ProphetSecretary.Limiting
