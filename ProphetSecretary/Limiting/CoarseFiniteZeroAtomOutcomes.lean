import ProphetSecretary.Limiting.CoarseFiniteZeroAtomScoreLimit
import ProphetSecretary.Limiting.FiniteCutoffScoreOutcomes

/-!
# Actual direct coarse zero-atom reward and duration covariance limits

The complete zero-atom likelihood score multiplies the actual finite
execution. Bounded coordinate tests are removed only using the established
outcome ranges on the actual finite and limiting laws.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_zeroAtom_outcomes_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (N : ℕ → ℕ) (hN : ∀ m, 0<N m)
    (hNLim : Tendsto (fun m => (N m:ℝ)) atTop atTop)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (d b : ℝ) (hd : 0≤d) (hdb : d≤b)
    (H : ℝ≥0) (hBH : (B.cap:ℝ)≤H) (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hκCap : ∀ m, ∀ᵐ x ∂κ m, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d) atTop (𝓝 B.intensity))
    (hAtom : (B.intensity:Measure ℝ) {b}=0) (hb : 0<b)
    (hZero : ∀ m, (1/2:ℝ)≤(κ m).real {0})
    (hBand : ∀ m, (κ m).real (Ioi b)=(B.intensity:Measure ℝ).real (Ioi b)/(N m:ℝ))
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    : let π := B.valueThresholdPolicy hw.le hc.le
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let Γ := fun m => π.finiteCutoffEvaluation (N m) d
    let s := fun m => completeScore (fun _ : Fin (N m) => bandScore (κ m) (Ioi b))
    Tendsto (fun m => ∫ ω : (Γ m).World, s m (fun j => ω.1 (j.natAdd n))*(Γ m).realizedReward ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()))) ∧
    Tendsto (fun m => ∫ ω : (Γ m).World, s m (fun j => ω.1 (j.natAdd n))*(Γ m).realizedDuration ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let s := fun m => completeScore (fun _ : Fin (N m) => bandScore (κ m) (Ioi b))
  have hs (m) : Measurable (s m) := measurable_completeScore
    (fun _ => measurable_bandScore (κ m) measurableSet_Ioi)
  have hsInt (m) : Integrable (s m) (Q m).valuesLaw := by
    simpa only [s,Q,Model.iidOfferInstance,Model.Instance.valuesLaw,pow_one] using completeScore_integrable_pow (fun _ : Fin (N m) => κ m)
      (fun _ : Fin (N m) => bandScore (κ m) (Ioi b))
      (fun _ => measurable_bandScore (κ m) measurableSet_Ioi)
      (fun _ => Filter.Eventually.of_forall (bandScore_abs_le_one (κ m) (not_lt.mpr hb.le) (hZero m))) 1
  have hExec (m) := π.finiteCutoffEvaluation_score_coordinate_tests (Ps m) (Q m) d H (hPCap m) (fun _ => hκCap m)
    (s m) (hs m) (hsInt m)
  have hR := B.coarse_finite_zeroAtom_observables_tendsto ha hw hc Ps N hN hNLim κ hκ d b hd hdb H hPCap hκCap
    hPWeak hμWeak hAtom hb hZero hBand hSquares (coarseRewardTest n H)
  have hT := B.coarse_finite_zeroAtom_observables_tendsto ha hw hc Ps N hN hNLim κ hκ d b hd hdb H hPCap hκCap
    hPWeak hμWeak hAtom hb hZero hBand hSquares (coarseDurationTest n)
  have hBP (i) : ∀ᵐ x ∂B.individuals.law i, x≤(H:ℝ) := (B.individual_bounded i).mono (fun _ hx => hx.trans hBH)
  have hBμ : ∀ᵐ x ∂(B.intensity:Measure ℝ), x∈Ioc (0:ℝ) H :=
    B.intensity_supported.mono (fun _ hx => ⟨hx.1,hx.2.trans hBH⟩)
  have hRanges := hybrid_policy_outcome_ranges π B.individuals B.intensity H hBP hBμ
  have hRLim : (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
      coarseRewardTest n H (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ())) = ∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()) := by
    apply integral_congr_ae
    filter_upwards [hRanges] with v hv
    exact congrArg (fun x => ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*x)
      (boundedClamp_eq H hv.1)
  have hTLim : (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
      coarseDurationTest n (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ())) = ∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()) := by
    apply integral_congr_ae
    filter_upwards [hRanges] with v hv
    exact congrArg (fun x => ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*x)
      (boundedClamp_eq 1 hv.2)
  constructor
  · rw [hRLim] at hR
    exact hR.congr (fun m => by simpa [π,s,Q,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseRewardTest] using (hExec m).1.2.symm)
  · rw [hTLim] at hT
    exact hT.congr (fun m => by simpa [π,s,Q,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseDurationTest] using (hExec m).2.2.symm)
end ProphetSecretary.Limiting
