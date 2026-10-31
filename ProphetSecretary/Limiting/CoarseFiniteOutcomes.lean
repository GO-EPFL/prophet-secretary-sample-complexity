import ProphetSecretary.Limiting.CoarseFinitePoissonLimit
import ProphetSecretary.Limiting.FiniteCutoffScoreOutcomes

/-!
# Actual coarse reward and duration limits

Bounded coordinate tests of the actual finite execution are removed using the established
outcome ranges on the actual finite and limiting laws.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_outcomes_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m))
    (d : ℝ) (hd : 0≤d) (H : ℝ≥0) (hBH : (B.cap:ℝ)≤H)
    (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hQCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d) atTop (𝓝 B.intensity))
    {L : ℝ} (hL : 0≤L) (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (Q m).tailCount d≤L) (hRare : ∀ m i, ((Q m).law i).real (Ioi d)≤δ m)
    : let π := B.valueThresholdPolicy hw.le hc.le
    let Γ := fun m => π.finiteCutoffEvaluation (sizes m) d
    Tendsto (fun m => ∫ ω : (Γ m).World, (Γ m).realizedReward ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, 
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()))) ∧
    Tendsto (fun m => ∫ ω : (Γ m).World, (Γ m).realizedDuration ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, 
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  have hs (m : ℕ) : Measurable (fun _ : Fin (sizes m) → ℝ => (1:ℝ)) := measurable_const
  have hsInt (m : ℕ) : Integrable (fun _ : Fin (sizes m) → ℝ => (1:ℝ)) (Q m).valuesLaw := integrable_const 1
  have hExec (m) := π.finiteCutoffEvaluation_score_coordinate_tests (Ps m) (Q m) d H (hPCap m) (hQCap m)
    (fun _ => (1:ℝ)) (hs m) (hsInt m)
  have hR := B.coarse_finite_observables_tendsto ha hw hc Ps sizes Q d hd H hPCap hQCap
    hPWeak hμWeak hL δ hδ hδLim hTail hRare (coarseRewardTest n H)
  have hT := B.coarse_finite_observables_tendsto ha hw hc Ps sizes Q d hd H hPCap hQCap
    hPWeak hμWeak hL δ hδ hδLim hTail hRare (coarseDurationTest n)
  have hBP (i) : ∀ᵐ x ∂B.individuals.law i, x≤(H:ℝ) := (B.individual_bounded i).mono (fun _ hx => hx.trans hBH)
  have hBμ : ∀ᵐ x ∂(B.intensity:Measure ℝ), x∈Ioc (0:ℝ) H :=
    B.intensity_supported.mono (fun _ hx => ⟨hx.1,hx.2.trans hBH⟩)
  have hRanges := hybrid_policy_outcome_ranges π B.individuals B.intensity H hBP hBμ
  have hRLim : (∫ v, 
      coarseRewardTest n H (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ())) = ∫ v, 
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()) := by
    apply integral_congr_ae
    filter_upwards [hRanges] with v hv
    exact boundedClamp_eq H hv.1
  have hTLim : (∫ v, 
      coarseDurationTest n (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ())) = ∫ v, 
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()) := by
    apply integral_congr_ae
    filter_upwards [hRanges] with v hv
    exact boundedClamp_eq 1 hv.2
  constructor
  · rw [hRLim] at hR
    exact hR.congr (fun m => by simpa [π,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseRewardTest] using (hExec m).1.2.symm)
  · rw [hTLim] at hT
    exact hT.congr (fun m => by simpa [π,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseDurationTest] using (hExec m).2.2.symm)
end ProphetSecretary.Limiting
