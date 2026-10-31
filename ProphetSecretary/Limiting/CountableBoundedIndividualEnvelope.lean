import ProphetSecretary.Limiting.CountableIndividualEnvelope

/-!
# Arbitrarily bounded individual likelihood directions

Dividing a centered score by K+1 reduces a finite bound K to the unit bound.
Rescaling the real parameter restores the original score. The actual density
is 1+θh(Xi) on the explicit neighborhood |θ|≤1/(4(K+1)).
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

private lemma normalized_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ x ∂μ, |h x| ≤ K) :
    ∀ᵐ x ∂μ, |h x/(K+1)| ≤ 1 := by
  have hC : 0 < K+1 := by linarith only [hK]
  filter_upwards [hb] with x hx
  rw [abs_div,abs_of_pos hC]
  apply (div_le_iff₀ hC).mpr
  linarith only [hx]

private lemma normalized_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → ℝ} {K : ℝ} (hm : ∫ x, h x ∂μ=0) :
    (∫ x, h x/(K+1) ∂μ)=0 := by rw [integral_div,hm,zero_div]

noncomputable def boundedIndividualLikelihoodPath (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ K)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) : CountableInstance :=
  B.individualLikelihoodPath i (fun x => h x/(K+1)) (hh.div_const (K+1))
    (normalized_bound hK hb) (normalized_mean hm) ((K+1)*θ)

lemma boundedIndividualLikelihoodPath_completeWorldLaw (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ K)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) {θ : ℝ}
    (hθ : |θ| ≤ (1/4)/(K+1)) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.boundedIndividualLikelihoodPath i h hh K hK hb hm θ).completeWorldLaw ν=
      ProphetSecretary.Probability.tiltLaw (B.completeWorldLaw ν) (fun v => h (v.2.1 i)) θ := by
  have hC : 0 < K+1 := by linarith only [hK]
  have hθN : |(K+1)*θ| ≤ 1/4 := by
    rw [abs_mul,abs_of_pos hC,mul_comm]
    exact (le_div_iff₀ hC).mp hθ
  unfold boundedIndividualLikelihoodPath
  rw [B.individualLikelihoodPath_of_mem _ _ _ _ _ hθN,
    B.individualLikelihoodTilt_completeWorldLaw _ _ _ _ _ _ hθN ν]
  unfold ProphetSecretary.Probability.tiltLaw
  congr 1
  funext v
  apply congrArg ENNReal.ofReal
  change 1+((K+1)*θ)*(h (v.2.1 i)/(K+1))=1+θ*h (v.2.1 i)
  field_simp [hC.ne']

/-- The individual-variable likelihood assertion of `lem:envelopes` for every
measurable centered score with a finite almost-sure bound. -/
theorem hasDerivAt_optimalScalarValue_boundedIndividualLikelihoodPath
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ K)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    HasDerivAt (fun θ => (B.boundedIndividualLikelihoodPath i h hh K hK hb hm θ).optimalScalarValue w c)
      ((B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c h) 0 := by
  let C := K+1
  let s := fun x => h x/C
  have hC : 0 < C := by dsimp only [C]; linarith only [hK]
  have hs : Measurable s := hh.div_const C
  have hsB : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |s x| ≤ 1 := normalized_bound hK hb
  have hs0 : ∫ x, s x ∂(B.individuals i : Measure ℝ)=0 := normalized_mean hm
  have hUnit := B.hasDerivAt_optimalScalarValue_individualLikelihoodPath hZero hw hc i s hs hsB hs0
  have hInner : HasDerivAt (fun θ : ℝ => C*θ) C 0 := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul C
  have hUnitAt : HasDerivAt (fun u => (B.individualLikelihoodPath i s hs hsB hs0 u).optimalScalarValue w c)
      ((B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c s) (C*0) := by
    simpa only [mul_zero] using hUnit
  have hComp := hUnitAt.comp 0 hInner
  have hDerivative : (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c s*C=
      (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c h := by
    unfold RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative
    have hFunction : (fun v : CompleteWorld (B.valuePolicy hw hc).Seed => (B.valuePolicy hw hc).scalarPayoff w c v*s (v.2.1 i))=
        fun v => ((B.valuePolicy hw hc).scalarPayoff w c v*h (v.2.1 i))/C := by
      funext v
      dsimp only [s]
      ring
    rw [hFunction,integral_div]
    exact div_mul_cancel₀ _ hC.ne'
  change HasDerivAt (fun θ => (B.boundedIndividualLikelihoodPath i h hh K hK hb hm θ).optimalScalarValue w c)
    ((B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c s*C) 0 at hComp
  rw [hDerivative] at hComp
  exact hComp

end ProphetSecretary.Limiting.CountableInstance
