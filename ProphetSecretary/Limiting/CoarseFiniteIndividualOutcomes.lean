import ProphetSecretary.Limiting.CoarseFiniteIndividualScoreLimit
import ProphetSecretary.Limiting.RetainedCutoffScoreOutcomes

/-!
# Actual retained-individual coarse covariance limits

The recentered retained-individual score multiplies the actual finite
execution. Bounded coordinate tests are removed only using the established
outcome ranges on the actual finite and limiting laws.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_individual_outcomes_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m))
    (d : ℝ) (hd : 0≤d) (H : ℝ≥0) (hBH : (B.cap:ℝ)≤H)
    (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hQCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d) atTop (𝓝 B.intensity))
    {L : ℝ} (hL : 0≤L) (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (Q m).tailCount d≤L) (hRare : ∀ m i, ((Q m).law i).real (Ioi d)≤δ m)
    (i : Fin n) (f : ℝ →ᵇ ℝ) : let π := B.valueThresholdPolicy hw.le hc.le
    let Γ := fun m => π.finiteCutoffEvaluation (sizes m) d
    Tendsto (fun m => ∫ ω : (Γ m).World, centeredBoundedScore ((Ps m).law i) f (ω.1 (i.castAdd (sizes m)))*(Γ m).realizedReward ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()))) ∧
    Tendsto (fun m => ∫ ω : (Γ m).World, centeredBoundedScore ((Ps m).law i) f (ω.1 (i.castAdd (sizes m)))*(Γ m).realizedDuration ω
      ∂((Ps m).appendIndependent (Q m)).worldLaw π.seedLaw) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let g := fun m (v : Model.World n π.Seed) => centeredBoundedScore ((Ps m).law i) f (v.1 i)
  have hg (m) : Measurable (g m) :=
    (continuous_centeredBoundedScore ((Ps m).law i) f).measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  have hgb (m v) : ‖g m v‖≤1 := centeredBoundedScore_abs_le_one ((Ps m).law i) f (v.1 i)
  have hExec (m) := π.finiteCutoffEvaluation_retained_score_coordinate_tests (Ps m) (Q m) d H (hPCap m) (hQCap m)
    (g m) (hg m) (hgb m)
  have hR := B.coarse_finite_individual_observables_tendsto ha hw hc Ps sizes Q d hd H hPCap hQCap
    hPWeak hμWeak hL δ hδ hδLim hTail hRare i f (coarseRewardTest n H)
  have hT := B.coarse_finite_individual_observables_tendsto ha hw hc Ps sizes Q d hd H hPCap hQCap
    hPWeak hμWeak hL δ hδ hδLim hTail hRare i f (coarseDurationTest n)
  have hBP (i) : ∀ᵐ x ∂B.individuals.law i, x≤(H:ℝ) := (B.individual_bounded i).mono (fun _ hx => hx.trans hBH)
  have hBμ : ∀ᵐ x ∂(B.intensity:Measure ℝ), x∈Ioc (0:ℝ) H :=
    B.intensity_supported.mono (fun _ hx => ⟨hx.1,hx.2.trans hBH⟩)
  have hRanges := hybrid_policy_outcome_ranges π B.individuals B.intensity H hBP hBμ
  have hRLim : (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
      coarseRewardTest n H (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ())) = ∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
        (B.valueRule w c).realizedReward 0 v ∂B.law (Measure.dirac ()) := by
    apply integral_congr_ae
    filter_upwards [hRanges] with v hv
    exact congrArg (fun x => centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*x)
      (boundedClamp_eq H hv.1)
  have hTLim : (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
      coarseDurationTest n (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ())) = ∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.law (Measure.dirac ()) := by
    apply integral_congr_ae
    filter_upwards [hRanges] with v hv
    exact congrArg (fun x => centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*x)
      (boundedClamp_eq 1 hv.2)
  constructor
  · rw [hRLim] at hR
    exact hR.congr (fun m => by simpa [π,g,Model.Instance.projectWorld,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseRewardTest] using (hExec m).1.2.symm)
  · rw [hTLim] at hT
    exact hT.congr (fun m => by simpa [π,g,Model.Instance.projectWorld,FiniteIntensityHybridInstance.valueThresholdPolicy,hybridOutcomeObservable,coarseDurationTest] using (hExec m).2.2.symm)
end ProphetSecretary.Limiting
