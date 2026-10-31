import ProphetSecretary.Limiting.CoarseFiniteCloudScoreLimit
import ProphetSecretary.Limiting.FiniteCutoffScoreOutcomes

/-!
# Actual coarse reward and duration covariance limits

The original complete residual likelihood score multiplies the actual finite
execution. Bounded coordinate tests are removed only using the established
outcome ranges on the actual finite and limiting laws.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_cloud_outcomes_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m))
    (d b : ℝ) (hd : 0≤d) (hdb : d≤b) (H : ℝ≥0) (hBH : (B.cap:ℝ)≤H)
    (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hQCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d) atTop (𝓝 B.intensity))
    (hAtom : (B.intensity:Measure ℝ) {b}=0)
    (hHalf : ∀ m i, ((Q m).law i).real (Ioi b)≤1/2)
    {L : ℝ} (hL : 0≤L) (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (Q m).tailCount d≤L) (hRare : ∀ m i, ((Q m).law i).real (Ioi d)≤δ m)
    : let π := B.valueThresholdPolicy hw.le hc.le
    let Γ := fun m => π.finiteCutoffEvaluation (sizes m) d
    let s := fun m => completeScore (fun i => compensatedBandScore ((Q m).law i) (Ioi b))
    Tendsto (fun m => ∫ ω : (Γ m).World, s m (fun j => ω.1 (j.natAdd n))*(Γ m).realizedReward ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()))) ∧
    Tendsto (fun m => ∫ ω : (Γ m).World, s m (fun j => ω.1 (j.natAdd n))*(Γ m).realizedDuration ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(B.intensity:Measure ℝ).real (Ioi b))*
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let s := fun m => completeScore (fun i => compensatedBandScore ((Q m).law i) (Ioi b))
  have hs (m) : Measurable (s m) := measurable_completeScore
    (fun i => measurable_compensatedBandScore ((Q m).law i) measurableSet_Ioi)
  have hsInt (m) : Integrable (s m) (Q m).valuesLaw := by
    simpa only [s,Model.Instance.valuesLaw,pow_one] using completeScore_integrable_pow (Q m).law
      (fun i => compensatedBandScore ((Q m).law i) (Ioi b))
      (fun i => measurable_compensatedBandScore ((Q m).law i) measurableSet_Ioi)
      (fun i => Filter.Eventually.of_forall (compensatedBandScore_abs_le_one ((Q m).law i) (hHalf m i))) 1
  have hExec (m) := π.finiteCutoffEvaluation_score_coordinate_tests (Ps m) (Q m) d H (hPCap m) (hQCap m)
    (s m) (hs m) (hsInt m)
  have hR := B.coarse_finite_cloud_observables_tendsto ha hw hc Ps sizes Q d b hd hdb H hPCap hQCap
    hPWeak hμWeak hAtom hHalf hL δ hδ hδLim hTail hRare (coarseRewardTest n H)
  have hT := B.coarse_finite_cloud_observables_tendsto ha hw hc Ps sizes Q d b hd hdb H hPCap hQCap
    hPWeak hμWeak hAtom hHalf hL δ hδ hδLim hTail hRare (coarseDurationTest n)
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
    exact hR.congr (fun m => by simpa [π,s,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseRewardTest] using (hExec m).1.2.symm)
  · rw [hTLim] at hT
    exact hT.congr (fun m => by simpa [π,s,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseDurationTest] using (hExec m).2.2.symm)
end ProphetSecretary.Limiting
