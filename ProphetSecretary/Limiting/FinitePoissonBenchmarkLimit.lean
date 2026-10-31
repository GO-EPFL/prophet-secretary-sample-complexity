import ProphetSecretary.Limiting.RareDesignBenchmark
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Prophet benchmarks of the direct finite Poisson approximants

The exact finite rare-design CDF tends to the actual Poisson void CDF.
The resulting benchmark convergence uses bounded layer cake and holds even
at zero intensity. It asserts no optimizing-policy convergence.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.mass_le_finitePoissonMultiplicity
    (B : FiniteIntensityHybridInstance n) (j : ℕ) :
    B.intensity.mass ≤ (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ≥0) := by
  have hceil := Nat.le_ceil ((B.intensity : Measure ℝ).real univ)
  have hn : Nat.ceil ((B.intensity : Measure ℝ).real univ) ≤
      bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j := by unfold bernoulliMultiplicity; omega
  exact_mod_cast hceil.trans (Nat.cast_le.mpr hn)

lemma FiniteIntensityHybridInstance.rareDesign_eq_finitePoissonApproximation
    (B : FiniteIntensityHybridInstance n) (j : ℕ) :
    rareDesign B.individuals B.intensity B.cap
      (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩)
      (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j)
      (bernoulliMultiplicity_positive _ _) (B.mass_le_finitePoissonMultiplicity j) =
      B.finitePoissonApproximation j := by
  rw [rareDesign_eq_zeroInflated _ _ _ _ _ _ _
    ((normalizedMarkOrZero_bounds B.intensity B.cap.property B.intensity_supported).mono fun _ hx => hx.1)]
  have hp : rareParameter B.intensity
      (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ≥0)
      (by exact_mod_cast bernoulliMultiplicity_positive ((B.intensity : Measure ℝ).real univ) j)
      (B.mass_le_finitePoissonMultiplicity j) =
      bernoulliProbability ((B.intensity : Measure ℝ).real univ) measureReal_nonneg j := by
    apply Subtype.ext
    change (((bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ≥0)⁻¹*B.intensity.mass : ℝ≥0) : ℝ) =
      (B.intensity : Measure ℝ).real univ/(bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ)
    rw [NNReal.coe_mul,NNReal.coe_inv,NNReal.coe_natCast]
    change _ = (B.intensity.mass : ℝ)/_
    ring
  rw [hp]
  rfl

/-- The direct approximants converge in the prophet benchmark, separately
from their already proved scalar-value convergence. -/
theorem FiniteIntensityHybridInstance.finitePoissonApproximation_expectedMaximum_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) :
    Tendsto (fun j => (B.finitePoissonApproximation j).expectedMaximum) atTop (𝓝 B.expectedMaximum) := by
  let rate := (B.intensity : Measure ℝ).real univ
  let ks := fun j => bernoulliMultiplicity rate j
  let hμ : ∀ᵐ x ∂(B.intensity : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap :=
    B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩
  let Qs := fun j => rareDesign B.individuals B.intensity B.cap hμ (ks j)
    (bernoulliMultiplicity_positive rate j) (B.mass_le_finitePoissonMultiplicity j)
  have hQR (j : ℕ) : ∀ᵐ x ∂(Qs j).valuesLaw, Model.Instance.maximum x ∈ Icc (0 : ℝ) B.cap := by
    have hQ := rareDesign_bounded B.individuals B.intensity B.cap B.individual_bounded hμ (ks j)
      (bernoulliMultiplicity_positive rate j) (B.mass_le_finitePoissonMultiplicity j)
    have hx : ∀ᵐ x ∂(Qs j).valuesLaw, ∀ i, x i ≤ (B.cap : ℝ) :=
      ae_all_iff.mpr (fun i => (measurePreserving_eval (Qs j).law i).quasiMeasurePreserving.ae (hQ i))
    exact hx.mono fun x h => ⟨Model.Instance.maximum_nonnegative x,Model.Instance.maximum_le x B.cap.property h⟩
  have hBR : ∀ᵐ v ∂hybridValueLaw B.individuals B.intensity, hybridMaximum 0 v ∈ Icc (0 : ℝ) B.cap := by
    filter_upwards [hybridValueLaw_values_bounds B.individuals B.intensity B.individual_bounded B.intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,hybridMaximum_le B.cap.property B.cap.property v (fun i => (hv i).2)⟩
  have hkLim : Tendsto ks atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro j
    dsimp only [ks,bernoulliMultiplicity,id_eq]
    omega
  have hCDF : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) B.cap),
      Tendsto (fun j => (Qs j).valuesLaw.real {v | Model.Instance.maximum v ≤ t}) atTop
        (𝓝 ((hybridValueLaw B.individuals B.intensity).real {v | hybridMaximum 0 v ≤ t})) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hPow := (Real.tendsto_one_add_div_pow_exp (-(B.intensity : Measure ℝ).real (Ioi t))).comp hkLim
    have hP : Tendsto (fun j => (1-(ks j : ℝ)⁻¹*(B.intensity : Measure ℝ).real (Ioi t))^(ks j)) atTop
        (𝓝 (Real.exp (-(B.intensity : Measure ℝ).real (Ioi t)))) := by
      convert hPow using 1
      funext j
      congr 1
      ring
    have h := hP.const_mul (∏ i, (B.individuals.law i).real (Iic t))
    simpa only [Qs,rareDesign_maximum_real_Iic _ _ _ _ _ _ _ ht.1.le,
      hybridMaximum_real_Iic _ _ ht.1.le ht.1.le,mul_comm] using h
  have hM := tendsto_integrals_of_bounded_cdf (fun j => (Qs j).valuesLaw)
    (hybridValueLaw B.individuals B.intensity) (fun _ => Model.Instance.maximum) (hybridMaximum 0)
    (fun _ => Model.Instance.measurable_maximum) (measurable_hybridMaximum 0) B.cap hQR hBR hCDF
  have hQs (j : ℕ) : Qs j = B.finitePoissonApproximation j := B.rareDesign_eq_finitePoissonApproximation j
  have he : (fun j => (Qs j).expectedMaximum) = fun j => (B.finitePoissonApproximation j).expectedMaximum := by
    funext j
    rw [hQs j]
  change Tendsto (fun j => (Qs j).expectedMaximum) atTop
    (𝓝 (hybridExpectedMaximum B.individuals B.intensity 0)) at hM
  rw [he] at hM
  simpa only [FiniteIntensityHybridInstance.expectedMaximum,ha,NNReal.coe_zero] using hM

end ProphetSecretary.Limiting
