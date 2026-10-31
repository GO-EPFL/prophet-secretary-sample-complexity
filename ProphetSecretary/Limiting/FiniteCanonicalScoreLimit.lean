import ProphetSecretary.Stability.ExpectedScoreStability
import ProphetSecretary.Stability.OutcomeStability
import ProphetSecretary.Analysis.TwoLimitScoreStability

/-!
# From actual coarse comparison policies to finite canonical score limits

The comparison uses one uniform finite outcome-stability modulus, then takes
first the finite-array limit at a fixed coarse policy and only afterwards
the coarse refinement limit. Every score is centered under its actual
marginal law; policy auxiliary seeds remain independent of the online data.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability

theorem finiteCanonical_score_tendsto_of_coarse
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ I : ℝ}
    (hH : 0≤H) (hδ : 0<δ) (hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d) (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (ws cs : ℕ → ℝ) (hw : ∀ m, δ≤ws m) (hc : ∀ m, δ≤cs m) (hNorm : ∀ m, ws m+cs m=1)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
    (hMeas : ∀ m i, Measurable (score m i)) (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (γ : ℕ → ∀ m, RandomizedPolicy (sizes m)) (bR bT r : ℕ → ℝ) (targetR targetT : ℝ)
    (hCoarseR : ∀ j, Tendsto (fun m => (γ j m).expectedRewardScore (P m) (score m)) atTop (𝓝 (bR j)))
    (hCoarseT : ∀ j, Tendsto (fun m => (γ j m).expectedDurationScore (P m) (score m)) atTop (𝓝 (bT j)))
    (hTargetR : Tendsto bR atTop (𝓝 targetR)) (hTargetT : Tendsto bT atTop (𝓝 targetT))
    (hRegret : ∀ j, Tendsto (fun m => optimalScalarValue (P m) (ws m) (cs m)-
      (γ j m).scalarObjective (P m) (ws m) (cs m)) atTop (𝓝 (r j)))
    (hRefine : Tendsto r atTop (𝓝 (0:ℝ))) :
    let ρ := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
      (hδ.le.trans (hw m)) (hδ.le.trans (hc m))
    Tendsto (fun m => (ρ m).expectedRewardScore (P m) (score m)) atTop (𝓝 targetR) ∧
    Tendsto (fun m => (ρ m).expectedDurationScore (P m) (score m)) atTop (𝓝 targetT) := by
  let ρ := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
    (hδ.le.trans (hw m)) (hδ.le.trans (hc m))
  obtain ⟨Ω,_hΩ,hMono,_hZero,hOmega,hError,_hNeg⟩ := finite_outcome_stability_with_profile
    sizes P hH hδ hCap L hL hTail
  have hPair (j m) := (γ j m).expectedScore_stability (P m) hH (hCap m)
    (hδ.trans_le (hw m)) (hδ.le.trans (hc m)) (score m) (hMeas m) (hBound m) (hMean m) (hInfo m)
    (hError m (ws m) (cs m) (hw m) (hc m) (hNorm m) (γ j m))
  constructor
  · apply ProphetSecretary.Analysis.tendsto_of_twoLimit_scoreStability (by positivity : 0≤2*I*(H+1))
      hMono hOmega hCoarseR hTargetR hRegret hRefine
    intro j
    exact Filter.Eventually.of_forall (fun m => by
      rw [abs_sub_comm]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hPair j m))
  · apply ProphetSecretary.Analysis.tendsto_of_twoLimit_scoreStability (by positivity : 0≤2*I*(H+1))
      hMono hOmega hCoarseT hTargetT hRegret hRefine
    intro j
    exact Filter.Eventually.of_forall (fun m => by
      rw [abs_sub_comm]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hPair j m))
end ProphetSecretary.Limiting
