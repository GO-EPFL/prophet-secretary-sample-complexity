import ProphetSecretary.Limiting.CoarseFiniteOutcomes
import ProphetSecretary.Limiting.OrderedResidualEvaluationInputs
import ProphetSecretary.Limiting.WeightedCoarsePolicy
import ProphetSecretary.Model.ScalarObjectiveBounds

/-!
# Coarse comparison policies on the original extracted finite instances

The retained dimension and cutoff are fixed before taking the finite-array
limit. A waiting policy totalizes the finitely many indices before the
residual prefix contains the retained prefix.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting

noncomputable def originalCoarsePolicy {n K : ℕ} (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (π : RandomizedHybridPolicy K) (d : ℝ) : Model.RandomizedPolicy n :=
  if h : K≤N then weightedCoarsePolicy P wgt N h π d else Model.RandomizedPolicy.waiting n

theorem OrderedBandConvergence.original_coarse_outcomes_tendsto
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (K : ℕ)
    (d : ℝ) (hd : 0<d) (hAtom : B.intensity {d}=0)
    (hWeak : Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d)
      atTop (𝓝 (B.intensityAbove d (by simpa [hZero] using hd))))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    let D := B.truncation K d (by simpa [hZero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => (originalCoarsePolicy (P m) wgt (Ns m) π d).expectedReward (P m)) atTop
      (𝓝 (∫ v, (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (originalCoarsePolicy (P m) wgt (Ns m) π d).expectedDuration (P m)) atTop
      (𝓝 (∫ v, (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  let D := B.truncation K d (by simpa [hZero] using hd)
  let π := D.valueThresholdPolicy hw.le hc.le
  let Ps := fun m => weightOrderedPrefix (P m) wgt K
  let Q := fun m => weightOrderedRemainder (P m) wgt (Ns m)
  let δ := fun m => residualTailSup (fun j => weightOrderedPaddedLaw (P m) wgt j) (Ns m) d
  obtain ⟨hμWeak,⟨L,hL,hTail⟩,hδLim⟩ := h.residual_evaluation_inputs hZero Ns hNs d hd hAtom hWeak
  have hLim := D.coarse_finite_outcomes_tendsto hZero hw hc Ps sizes Q d hd.le B.cap (le_refl _)
    (fun m => weightOrderedPrefix_bounded (P m) wgt K B.cap.property (hCap m))
    (fun m => weightOrderedRemainder_bounded (P m) wgt (Ns m) B.cap.property (hCap m))
    (h.prefix_marginal_tendsto K) hμWeak hL δ
    (fun m => residualTailSup_nonneg _ _ _) hδLim hTail
    (fun m i => weightOrderedRemainder_tail_le_sup (P m) wgt (Ns m) d i)
  constructor
  · apply hLim.1.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hm
    have hm' : K≤Ns m := hm
    have hγ : originalCoarsePolicy (P m) wgt (Ns m) π d=weightedCoarsePolicy (P m) wgt (Ns m) hm' π d := by
      unfold originalCoarsePolicy
      exact dif_pos hm'
    exact (weightedCoarsePolicy_expectedReward (P m) wgt (Ns m) hm' π d).symm.trans
      ((congrArg (fun ρ : Model.RandomizedPolicy (sizes m) => ρ.expectedReward (P m)) hγ).symm)
  · apply hLim.2.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hm
    have hm' : K≤Ns m := hm
    have hγ : originalCoarsePolicy (P m) wgt (Ns m) π d=weightedCoarsePolicy (P m) wgt (Ns m) hm' π d := by
      unfold originalCoarsePolicy
      exact dif_pos hm'
    exact (weightedCanonicalCoarsePolicy_expectedDuration (P m) wgt (Ns m) hm' D hw hc d).symm.trans
      ((congrArg (fun ρ : Model.RandomizedPolicy (sizes m) => ρ.expectedDuration (P m)) hγ).symm)
end ProphetSecretary.Limiting
