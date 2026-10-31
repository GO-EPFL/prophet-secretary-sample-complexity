import ProphetSecretary.Limiting.OriginalCoarseOutcomes
import ProphetSecretary.Limiting.HybridBellmanIdentity

/-!
# Actual coarse regret under converging scalar weights

The finite-array limit is taken with a fixed coarse callback. Its limiting
scalar objective is the optimal value of the fixed hybrid truncation. The
weights in the finite objective may converge independently of that callback.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting

theorem OrderedBandConvergence.original_coarse_regret_tendsto
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (K : ℕ)
    (d : ℝ) (hd : 0<d) (hAtom : B.intensity {d}=0)
    (hWeak : Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d)
      atTop (𝓝 (B.intensityAbove d (by simpa [hZero] using hd))))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (ws cs : ℕ → ℝ)
    (hws : Tendsto ws atTop (𝓝 w)) (hcs : Tendsto cs atTop (𝓝 c))
    (hV : Tendsto (fun m => Model.optimalScalarValue (P m) (ws m) (cs m)) atTop (𝓝 (B.optimalScalarValue w c))) :
    let D := B.truncation K d (by simpa [hZero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => Model.optimalScalarValue (P m) (ws m) (cs m)-
      (originalCoarsePolicy (P m) wgt (Ns m) π d).scalarObjective (P m) (ws m) (cs m)) atTop
      (𝓝 (B.optimalScalarValue w c-D.optimalScalarValue w c)) := by
  let D := B.truncation K d (by simpa [hZero] using hd)
  let π := D.valueThresholdPolicy hw.le hc.le
  let γ := fun m => originalCoarsePolicy (P m) wgt (Ns m) π d
  obtain ⟨hR,hT⟩ := h.original_coarse_outcomes_tendsto hZero hCap Ns hNs K d hd hAtom hWeak hw hc
  have hOpt := D.valueThresholdPolicy_optimal hZero hw hc.le
  rw [RandomizedHybridPolicy.scalarObjective_eq] at hOpt
  change w*(∫ v, (D.valueRule w c).realizedReward D.terminal v ∂D.law (Measure.dirac ()) )+
    c*(∫ v, (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))=D.optimalScalarValue w c at hOpt
  have hDz : (D.terminal:ℝ)=0 := by simp only [D,CountableInstance.truncation,hZero,NNReal.coe_zero]
  rw [hDz] at hOpt
  have hJ := (hws.mul hR).add (hcs.mul hT)
  rw [hOpt] at hJ
  have hJ' : Tendsto (fun m => (γ m).scalarObjective (P m) (ws m) (cs m)) atTop
      (𝓝 (D.optimalScalarValue w c)) := by
    apply hJ.congr
    intro m
    exact ((γ m).scalarObjective_eq (P m) ((P m).integrable_maximum_of_bounded (hCap m)) (ws m) (cs m)).symm
  exact hV.sub hJ'
end ProphetSecretary.Limiting
