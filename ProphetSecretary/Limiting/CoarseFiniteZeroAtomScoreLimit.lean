import ProphetSecretary.Limiting.CoarseFinitePoissonLimit
import ProphetSecretary.Limiting.ThresholdedWorldZeroAtomScore
import ProphetSecretary.Limiting.HybridFixedCenteredBandScoreWeak

/-!
# Zero-atom score limits for fixed coarse policies on direct approximants

The virtual count is fixed throughout each likelihood experiment. The score
compensates only at zero. Its actual L² count approximation and marked-Poisson
coupling transfer bounded outcome tests before the coarse policy is refined.
No total-first-moment bound is required.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_zeroAtom_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (N : ℕ → ℕ) (hN : ∀ m, 0<N m)
    (hNLim : Tendsto (fun m => (N m:ℝ)) atTop atTop)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (d b : ℝ) (hd : 0≤d) (hdb : d≤b)
    (H : ℝ≥0) (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hκCap : ∀ m, ∀ᵐ x ∂κ m, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d) atTop (𝓝 B.intensity))
    (hAtom : (B.intensity:Measure ℝ) {b}=0) (hb : 0<b)
    (hZero : ∀ m, (1/2:ℝ)≤(κ m).real {0})
    (hBand : ∀ m, (κ m).real (Ioi b)=(B.intensity:Measure ℝ).real (Ioi b)/(N m:ℝ))
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    let π := B.valueThresholdPolicy hw.le hc.le
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    Tendsto (fun m => ∫ ω : Model.World (N m) (Model.World n Unit),
      completeScore (fun _ : Fin (N m) => bandScore (κ m) (Ioi b)) ω.1*
        hybridOutcomeObservable π Φ (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)
      ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
        ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let G := hybridOutcomeObservable π Φ
  let μ := fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d
  let a := (B.intensity:Measure ℝ).real (Ioi b)
  let A := fun m => ∫ ω : Model.World (N m) (Model.World n Unit),
    completeScore (fun _ : Fin (N m) => bandScore (κ m) (Ioi b)) ω.1*
      G (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)
  let C := fun m => ∫ v : HybridWorld n Unit,
    ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-a)*G (countingMeasure v.1,v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw
  have hG : Measurable G := measurable_hybridOutcomeObservable π Φ Φ.continuous.measurable
  have hGBound (z) : |G z|≤‖Φ‖ := by
    change ‖G z‖≤‖Φ‖
    exact Φ.norm_coe_le_norm
      ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2),
        π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2)),z.2)
  have hError (m) : |A m-C m|≤Real.sqrt (‖Φ‖^2*(2*a^2/(N m:ℝ)))+
      Real.sqrt (4*‖Φ‖^2*a*((N m:ℝ)*((κ m).real (Ioi d))^2)) :=
    thresholdedWorld_zeroAtomScore_poisson_error (κ m) (hκ m) ((Ps m).worldLaw π.seedLaw)
      (N m) (hN m) d measurableSet_Ioi (Ioi_subset_Ioi hdb) (not_lt.mpr hb.le) (hZero m) (hBand m)
      G hG (norm_nonneg Φ) hGBound
  have hRate1 : Tendsto (fun m => Real.sqrt (‖Φ‖^2*(2*a^2/(N m:ℝ)))) atTop (𝓝 (0:ℝ)) := by
    have hInner : Tendsto (fun m => ‖Φ‖^2*(2*a^2/(N m:ℝ))) atTop (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using (tendsto_const_nhds.div_atTop hNLim).const_mul (‖Φ‖^2)
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hInner
  have hRate2 : Tendsto (fun m => Real.sqrt (4*‖Φ‖^2*a*((N m:ℝ)*((κ m).real (Ioi d))^2))) atTop (𝓝 (0:ℝ)) := by
    have hInner : Tendsto (fun m => 4*‖Φ‖^2*a*((N m:ℝ)*((κ m).real (Ioi d))^2)) atTop (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using hSquares.const_mul (4*‖Φ‖^2*a)
    simpa only [Function.comp_def,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hInner
  have hDiff : Tendsto (fun m => A m-C m) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hRate : Tendsto (fun m => Real.sqrt (‖Φ‖^2*(2*a^2/(N m:ℝ)))+
        Real.sqrt (4*‖Φ‖^2*a*((N m:ℝ)*((κ m).real (Ioi d))^2))) atTop (𝓝 (0:ℝ)) := by
      simpa only [zero_add] using hRate1.add hRate2
    simpa only [sub_zero,Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hError hRate
  have hActual := B.fixed_valueRule_centeredBand_observables_tendsto ha hw hc Ps B.individuals hPWeak hμWeak b hAtom Φ
  have hMass (m) : (μ m:Measure ℝ).real (Ioi b)=a := by
    have h := thresholdMarkIntensity_sum_band_real (Q m).law d measurableSet_Ioi (Ioi_subset_Ioi hdb)
    change (μ m:Measure ℝ).real (Ioi b)=∑ _i : Fin (N m), (κ m).real (Ioi b) at h
    rw [h]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hBand m]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hN m)))
  have hCEq (m) : C m=(∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(μ m:Measure ℝ).real (Ioi b))*
      Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) := by
    unfold C
    rw [hMass m]
    exact integral_congr_ae ((hybridOutcomeObservable_eq_ae π (Ps m) (μ m) H (hPCap m)
      (thresholdMarkIntensity_sum_supported (Q m) hd (fun _ => hκCap m)) Φ).mono (fun v hv =>
        congrArg (fun x => ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-a)*x) hv))
  have hCLim := hActual.congr (fun m => (hCEq m).symm)
  change Tendsto A atTop (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
    Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2) ∂B.law (Measure.dirac ())))
  simpa only [sub_add_cancel,zero_add,FiniteIntensityHybridInstance.law] using hDiff.add hCLim
end ProphetSecretary.Limiting
