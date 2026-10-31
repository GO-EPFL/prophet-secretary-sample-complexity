import ProphetSecretary.Limiting.ThresholdedWorldBandScorePoisson

/-!
# Uniform rare-array limit for complete band-score expectations

A common expected-tail-count bound and a vanishing largest occurrence
probability give an explicit dimension-independent square-root error. The
auxiliary law and bounded analytical payoff may vary with the array index.
-/
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

theorem thresholdedWorld_bandScore_error_le_tailBound (P : Model.Instance n) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d)
    (g : (Measure Point) × Aux → ℝ) (hg : Measurable g) {D K δ : ℝ} (hD : 0≤D) (hK : 0≤K) (hδ : 0≤δ)
    (hb : ∀ q, |g q|≤D) (hTail : P.tailCount d≤K) (hRare : ∀ i, (P.law i).real (Ioi d)≤δ) :
    let a := ∑ i, (P.law i).real B
    let μ := ∑ i, thresholdMarkIntensity (P.law i) d
    |(∫ ω : Model.World n Aux, centeredIndependentBandCount P.law B ω.1*
        g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂P.worldLaw ν)-
      ∫ q : Configuration × Aux, ((pointCount (univ ×ˢ B) q.1:ℝ)-a)*g (countingMeasure q.1,q.2)
        ∂(configurationLaw μ).prod ν| ≤ Real.sqrt (4*D^2*K^2*δ) := by
  apply (thresholdedWorld_bandScore_poisson_error P ν d hB hAbove g hg hD hb).trans
  apply Real.sqrt_le_sqrt
  have hBand : (∑ i, (P.law i).real B)≤K := by
    apply (Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => measureReal_mono (μ := P.law i) hAbove)).trans
    exact hTail
  have hSq : (∑ i, ((P.law i).real (Ioi d))^2)≤δ*K := by
    calc
      _ ≤ ∑ i, δ*(P.law i).real (Ioi d) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hRare i) measureReal_nonneg
      _ = δ*P.tailCount d := by
        change (∑ i, δ*(P.law i).real (Ioi d))=δ*(∑ i, (P.law i).real (Ioi d))
        rw [Finset.mul_sum]
      _ ≤ δ*K := mul_le_mul_of_nonneg_left hTail hδ
  have hMul := mul_le_mul hBand hSq (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hK
  have hScale := mul_le_mul_of_nonneg_left hMul (show 0≤4*D^2 by positivity)
  nlinarith only [hScale]

/-- The explicit bound applies when the finite instance sizes vary. The
largest tail probability vanishes before any later cutoff-removal limit. -/
theorem thresholdedWorld_bandScore_difference_tendsto_zero
    (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (ν : ℕ → Measure Aux) [∀ m, IsProbabilityMeasure (ν m)]
    (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d)
    (g : ℕ → (Measure Point) × Aux → ℝ) (hg : ∀ m, Measurable (g m))
    {D K : ℝ} (hD : 0≤D) (hK : 0≤K) (hb : ∀ m q, |g m q|≤D)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (P m).tailCount d≤K) (hRare : ∀ m i, ((P m).law i).real (Ioi d)≤δ m) :
    Tendsto (fun m =>
      (∫ ω : Model.World (sizes m) Aux, centeredIndependentBandCount (P m).law B ω.1*
        g m (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(P m).worldLaw (ν m))-
      ∫ q : Configuration × Aux, ((pointCount (univ ×ˢ B) q.1:ℝ)-∑ i, ((P m).law i).real B)*
        g m (countingMeasure q.1,q.2) ∂(configurationLaw (∑ i, thresholdMarkIntensity ((P m).law i) d)).prod (ν m))
      atTop (𝓝 (0:ℝ)) := by
  have hRate : Tendsto (fun m => Real.sqrt (4*D^2*K^2*δ m)) atTop (𝓝 (0:ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp (hδLim.const_mul (4*D^2*K^2))
    simpa only [Function.comp_def,mul_zero,Real.sqrt_zero] using h
  have hBound := fun m => thresholdedWorld_bandScore_error_le_tailBound (P m) (ν m) d hB hAbove
    (g m) (hg m) hD hK (hδ m) (hb m) (hTail m) (hRare m)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero,Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hBound hRate
end ProphetSecretary.Limiting
