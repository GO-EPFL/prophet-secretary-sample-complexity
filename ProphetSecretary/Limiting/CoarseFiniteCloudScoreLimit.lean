import ProphetSecretary.Limiting.CoarseFinitePoissonLimit
import ProphetSecretary.Limiting.ThresholdedWorldCompensatedScore
import ProphetSecretary.Limiting.HybridFixedCenteredBandScoreWeak

/-!
# First finite-array limit for the original compensated cloud score

A fixed canonical coarse callback is evaluated on independent residual arrays.
Full-complement scores are first replaced by actual centered Poisson counts.
The cutoff and retained dimension stay fixed throughout this sequence limit.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_cloud_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m))
    (d b : ℝ) (hd : 0≤d) (hdb : d≤b) (H : ℝ≥0)
    (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hQCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d) atTop (𝓝 B.intensity))
    (hAtom : (B.intensity:Measure ℝ) {b}=0)
    (hHalf : ∀ m i, ((Q m).law i).real (Ioi b)≤1/2)
    {L : ℝ} (hL : 0≤L) (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (Q m).tailCount d≤L) (hRare : ∀ m i, ((Q m).law i).real (Ioi d)≤δ m)
    (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    let π := B.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => ∫ ω : Model.World (sizes m) (Model.World n Unit),
      completeScore (fun i => compensatedBandScore ((Q m).law i) (Ioi b)) ω.1*
      hybridOutcomeObservable π Φ
        (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)
      ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
        ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let G := hybridOutcomeObservable π Φ
  let μ := fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d
  let A := fun m => ∫ ω : Model.World (sizes m) (Model.World n Unit),
    completeScore (fun i => compensatedBandScore ((Q m).law i) (Ioi b)) ω.1*
    G (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)
  let C := fun m => ∫ v : HybridWorld n Unit,
    ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-∑ i, ((Q m).law i).real (Ioi b))*G (countingMeasure v.1,v.2)
    ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw
  have hG : Measurable G := measurable_hybridOutcomeObservable π Φ Φ.continuous.measurable
  have hGBound (z) : |G z|≤‖Φ‖ := by
    change ‖G z‖≤‖Φ‖
    exact Φ.norm_coe_le_norm
      ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2),
        π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2)),z.2)
  have hBandTail (m) : (Q m).tailCount b≤L := ((Q m).tailCount_antitone hdb).trans (hTail m)
  have hBandRare (m i) : ((Q m).law i).real (Ioi b)≤δ m :=
    (measureReal_mono (μ := (Q m).law i) (Ioi_subset_Ioi hdb)).trans (hRare m i)
  have hError (m : ℕ) : |A m-C m|≤Real.sqrt (‖Φ‖^2*(δ m*L))+Real.sqrt (4*‖Φ‖^2*L^2*δ m) := by
    apply (thresholdedWorld_compensatedScore_poisson_error (Q m) ((Ps m).worldLaw π.seedLaw) d
      measurableSet_Ioi (Ioi_subset_Ioi hdb) (hHalf m) G hG (norm_nonneg Φ) hGBound).trans
    apply add_le_add
    · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (finite_tail_square_sum_le (Q m) b (hδ m) (hBandTail m) (hBandRare m)) (sq_nonneg ‖Φ‖))
    · apply Real.sqrt_le_sqrt
      have hProd := mul_le_mul (hBandTail m)
        (finite_tail_square_sum_le (Q m) d (hδ m) (hTail m) (hRare m))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hL
      have hScale := mul_le_mul_of_nonneg_left hProd (show 0≤4*‖Φ‖^2 by positivity)
      change 4*‖Φ‖^2*(Q m).tailCount b*(∑ i, ((Q m).law i).real (Ioi d)^2)≤4*‖Φ‖^2*L^2*δ m
      nlinarith only [hScale]
  have hRate1 : Tendsto (fun m => Real.sqrt (‖Φ‖^2*(δ m*L))) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,mul_zero,zero_mul,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ((hδLim.mul_const L).const_mul (‖Φ‖^2))
  have hRate2 : Tendsto (fun m => Real.sqrt (4*‖Φ‖^2*L^2*δ m)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,mul_zero,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hδLim.const_mul (4*‖Φ‖^2*L^2))
  have hDiff : Tendsto (fun m => A m-C m) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hRate : Tendsto (fun m => Real.sqrt (‖Φ‖^2*(δ m*L))+Real.sqrt (4*‖Φ‖^2*L^2*δ m)) atTop (𝓝 (0:ℝ)) := by
      simpa only [zero_add] using hRate1.add hRate2
    simpa only [sub_zero,Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hError hRate
  have hActual := B.fixed_valueRule_centeredBand_observables_tendsto ha hw hc Ps B.individuals hPWeak hμWeak b hAtom Φ
  have hCEq (m : ℕ) : C m=(∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(μ m:Measure ℝ).real (Ioi b))*
      Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) := by
    have hMass := thresholdMarkIntensity_sum_band_real (Q m).law d measurableSet_Ioi (Ioi_subset_Ioi hdb)
    change (μ m:Measure ℝ).real (Ioi b)=∑ i, ((Q m).law i).real (Ioi b) at hMass
    unfold C
    rw [← hMass]
    exact integral_congr_ae ((hybridOutcomeObservable_eq_ae π (Ps m) (μ m) H (hPCap m)
      (thresholdMarkIntensity_sum_supported (Q m) hd (hQCap m)) Φ).mono (fun v hv =>
        congrArg (fun x => ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(μ m:Measure ℝ).real (Ioi b))*x) hv))
  have hCLim : Tendsto C atTop (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
      Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ()))) := by
    have hSeq : C=(fun m => ∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(μ m:Measure ℝ).real (Ioi b))*
      Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) := funext hCEq
    rw [hSeq]
    exact hActual
  change Tendsto A atTop (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
    Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2) ∂B.law (Measure.dirac ())))
  simpa only [sub_add_cancel,zero_add] using hDiff.add hCLim
end ProphetSecretary.Limiting
