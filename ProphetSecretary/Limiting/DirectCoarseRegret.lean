import ProphetSecretary.Limiting.DirectCoarseOutcomeLimit
import ProphetSecretary.Limiting.HybridBellmanIdentity

/-!
# Vanishing limiting regret of actual direct coarse policies

At a fixed retained prefix and cutoff, actual reward and duration convergence
identify the limiting coarse objective with the truncation's optimal scalar
value. Refining the prefix and cutoff can then use the proved countable value
limit, without imposing a total-first-moment bound.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance

theorem CountableInstance.direct_coarse_regret_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (ret N : ℕ → ℕ) (hRet : Tendsto ret atTop atTop) (hN : ∀ m, 0<N m)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (hCap : ∀ m, ∀ᵐ x ∂κ m, x≤(B.cap:ℝ))
    (K : ℕ) (d : ℝ) (hd : 0<d)
    (hμWeak : Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d) atTop
      (𝓝 (B.intensityAbove d (by simpa only [hZero,NNReal.coe_zero] using hd))))
    {L : ℝ} (hL : 0≤L) (hTail : ∀ m, (N m:ℝ)*(κ m).real (Ioi d)≤L)
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (hV : Tendsto (fun m => Model.optimalScalarValue
      ((B.individualPrefix (ret m)).appendIndependent (Model.iidOfferInstance (κ m) (hκ m) (N m))) w c)
      atTop (𝓝 (B.optimalScalarValue w c))) :
    let D := B.truncation K d (by simpa only [hZero,NNReal.coe_zero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
    Tendsto (fun m => Model.optimalScalarValue (P m) w c-
      (directCoarsePolicy (ret m) (N m) π d).scalarObjective (P m) w c) atTop
      (𝓝 (B.optimalScalarValue w c-D.optimalScalarValue w c)) := by
  have hdAbove : (B.terminal:ℝ)<d := by simpa only [hZero,NNReal.coe_zero] using hd
  let D := B.truncation K d hdAbove
  let π := D.valueThresholdPolicy hw.le hc.le
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
  let γ := fun m => directCoarsePolicy (ret m) (N m) π d
  obtain ⟨hR,hT⟩ := B.direct_coarse_outcomes_tendsto hZero ret N hRet hN κ hκ hCap K d hd hμWeak hL hTail hSquares hw hc
  have hOpt := D.valueThresholdPolicy_optimal hZero hw hc.le
  rw [RandomizedHybridPolicy.scalarObjective_eq] at hOpt
  change w*(∫ v, (D.valueRule w c).realizedReward D.terminal v ∂D.law (Measure.dirac ()))+
    c*(∫ v, (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))=D.optimalScalarValue w c at hOpt
  have hDZ : (D.terminal:ℝ)=0 := by simp only [D,CountableInstance.truncation,hZero,NNReal.coe_zero]
  rw [hDZ] at hOpt
  have hJ := (hR.const_mul w).add (hT.const_mul c)
  rw [hOpt] at hJ
  have hCapP (m) : ∀ i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ) :=
    (B.individualPrefix (ret m)).appendIndependent_bounded (Q m)
      (fun i => (B.individual_supported i.val).mono (fun _ hx => hx.2)) (fun _ => hCap m)
  have hJ' : Tendsto (fun m => (γ m).scalarObjective (P m) w c) atTop (𝓝 (D.optimalScalarValue w c)) := by
    apply hJ.congr
    intro m
    exact ((γ m).scalarObjective_eq (P m) ((P m).integrable_maximum_of_bounded (hCapP m)) w c).symm
  exact hV.sub hJ'
end ProphetSecretary.Limiting
