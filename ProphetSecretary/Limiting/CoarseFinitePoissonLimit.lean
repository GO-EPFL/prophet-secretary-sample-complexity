import ProphetSecretary.Limiting.CoarsePoissonObservable
import ProphetSecretary.Limiting.ThresholdedWorldBandScoreLimit
import ProphetSecretary.Limiting.HybridValuePolicy

/-!
# First finite-array limit for a fixed canonical coarse policy

The cutoff and retained prefix are fixed before this sequence limit. Actual
marked Poisson comparison and canonical branch continuity transfer bounded
outcome/data tests from independent finite residual offers to the fixed
limiting hybrid model.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting

lemma finite_tail_square_sum_le {r : ℕ} (Q : Model.Instance r) (d : ℝ) {δ L : ℝ}
    (hδ : 0≤δ) (hTail : Q.tailCount d≤L) (hRare : ∀ i, (Q.law i).real (Ioi d)≤δ) :
    (∑ i, ((Q.law i).real (Ioi d))^2)≤δ*L := by
  calc
    _ ≤ δ*Q.tailCount d := by
      change (∑ i, ((Q.law i).real (Ioi d))^2)≤δ*(∑ i, (Q.law i).real (Ioi d))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      simpa only [pow_two] using (mul_le_mul_of_nonneg_right (hRare i) measureReal_nonneg)
    _ ≤ δ*L := mul_le_mul_of_nonneg_left hTail hδ

variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m))
    (d : ℝ) (hd : 0≤d) (H : ℝ≥0)
    (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hQCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d) atTop (𝓝 B.intensity))
    {L : ℝ} (_hL : 0≤L) (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (Q m).tailCount d≤L) (hRare : ∀ m i, ((Q m).law i).real (Ioi d)≤δ m)
    (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    let π := B.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => ∫ ω : Model.World (sizes m) (Model.World n Unit),
      hybridOutcomeObservable π Φ
        (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)
      ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)) atTop
      (𝓝 (∫ v, Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
        ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let G := hybridOutcomeObservable π Φ
  let μ := fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d
  let A := fun m => ∫ ω : Model.World (sizes m) (Model.World n Unit),
    G (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)
  let C := fun m => ∫ v, G (countingMeasure v.1,v.2) ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw
  have hG : Measurable G := measurable_hybridOutcomeObservable π Φ Φ.continuous.measurable
  have hGBound (z) : |G z|≤‖Φ‖ := by
    change ‖G z‖≤‖Φ‖
    exact Φ.norm_coe_le_norm
      ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2),
        π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2)),z.2)

  have hError (m : ℕ) : |A m-C m|≤2*‖Φ‖*(δ m*L) := by
    apply (thresholdedWorld_poisson_observable_error (Q m) ((Ps m).worldLaw π.seedLaw) d G hG (norm_nonneg Φ) hGBound).trans
    exact mul_le_mul_of_nonneg_left (finite_tail_square_sum_le (Q m) d (hδ m) (hTail m) (hRare m)) (by positivity)
  have hRate : Tendsto (fun m => 2*‖Φ‖*(δ m*L)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,zero_mul] using (hδLim.mul_const L).const_mul (2*‖Φ‖)
  have hDiff : Tendsto (fun m => A m-C m) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero,Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hError hRate
  have hActual := B.fixed_valueRule_observables_tendsto ha hw hc Ps B.individuals hPWeak hμWeak Φ
  have hCEq (m : ℕ) : C m=(∫ v, Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) :=
    integral_congr_ae (hybridOutcomeObservable_eq_ae π (Ps m) (μ m) H (hPCap m)
      (thresholdMarkIntensity_sum_supported (Q m) hd (hQCap m)) Φ)
  have hCLim : Tendsto C atTop (𝓝 (∫ v, Φ (((B.valueRule w c).realizedReward 0 v,
      (B.valueRule w c).realizedDuration v),v.2) ∂B.law (Measure.dirac ()))) := by
    have hSeq : C=(fun m => ∫ v, Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) := funext hCEq
    rw [hSeq]
    exact hActual
  have h := hDiff.add hCLim
  simpa only [sub_add_cancel,zero_add] using h
end ProphetSecretary.Limiting
