import ProphetSecretary.Limiting.CappedIntensityNormalization
import ProphetSecretary.Limiting.BernoulliScale

/-!
# A cap-uniform value error for finite Bernoulli designs

The virtual probability and multiplicity retain exactly the original finite
intensity mass. Capping fixes their zero atom and commutes with intensity
normalization. The actual all-policy Poisson error is bounded by the original
ambient cap, independently of the chosen positive cap and duration coefficient.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
variable {n k : ℕ}

lemma cappedBernoulliDesign_value_error (B : FiniteIntensityHybridInstance n)
    (hZero : B.terminal=0) (hμ : B.intensity≠0) (K : ℝ≥0) (hK : 0<K)
    (p : unitInterval) (hRate : (B.intensity : Measure ℝ).real univ=(k:ℝ)*(p:ℝ))
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    |Model.optimalScalarValue ((finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
        (B.normalizedMark_nonnegative hμ) p k).cap K) w c-(B.capAt K hK).optimalScalarValue w c|≤
      w*(B.cap:ℝ)*((k:ℝ)*(p:ℝ)^2+(Real.pi/2)*Real.sqrt ((k:ℝ)*(p:ℝ)^2)) := by
  let D := B.capAt K hK
  have hDμ : D.intensity≠0 := finiteMeasure_cap_nonzero B.intensity hμ K
  have hMass : D.intensity.mass=B.intensity.mass := finiteMeasure_cap_mass B.intensity K
  have hRateD : (D.intensity : Measure ℝ).real univ=(k:ℝ)*(p:ℝ) := by
    change (D.intensity.mass:ℝ)=_
    rw [hMass]
    exact hRate
  have hNorm : D.intensity.normalize=cappedMarkLaw B.intensity.normalize K := finiteMeasure_cap_normalize B.intensity hμ K
  have hFin : (finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
      (B.normalizedMark_nonnegative hμ) p k).cap K=
      finitePoissonDesign D.individuals (D.intensity.normalize : Measure ℝ) (D.normalizedMark_nonnegative hDμ) p k := by
    refine (finitePoissonDesign_cap B.individuals B.intensity.normalize (B.normalizedMark_nonnegative hμ) p k K).trans ?_
    apply Model.Instance.eq_of_law_eq
    funext i
    induction i using Fin.addCases with
    | left i => simp only [finitePoissonDesign,appendIID,Fin.addCases_left];rfl
    | right j =>
      simp only [finitePoissonDesign,appendIID,Fin.addCases_right]
      exact congrArg (fun κ : ProbabilityMeasure ℝ => zeroInflatedLaw (κ : Measure ℝ) p) hNorm.symm
  have hCompare := D.BernoulliDesignValue_abs_difference_le hZero hDμ p hRateD hw hc
  dsimp only at hCompare
  rw [←hFin] at hCompare
  have hMean : (∫ x, x ∂(D.intensity.normalize : Measure ℝ))≤(B.cap:ℝ) := by
    have hSupp := (normalized_ae D.intensity hDμ D.intensity_supported).mono fun _ hx => hx.2
    have h := integral_mono_ae (D.normalizedMark_integrable hDμ) (integrable_const (B.cap:ℝ)) hSupp
    simpa only [id_eq,integral_const,probReal_univ,one_smul] using h
  apply hCompare.trans
  calc
    _ = w*(∫ x, x ∂(D.intensity.normalize : Measure ℝ))*
        ((k:ℝ)*(p:ℝ)^2+(Real.pi/2)*Real.sqrt ((k:ℝ)*(p:ℝ)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMean hw.le) (by positivity)

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
