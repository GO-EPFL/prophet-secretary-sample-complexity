import ProphetSecretary.Limiting.OrderedAllContinuityResidual
import ProphetSecretary.Limiting.OrderedRemainderTailBounds
import ProphetSecretary.Limiting.ThresholdedOfferLaw

/-!
# Evaluation inputs supplied by ordered finite-array extraction

The retained marginal laws and anonymous residual intensities are the actual
laws of the padded finite blocks. A single residual schedule therefore gives
the independent finite-array inputs at every positive cloud continuity level.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting

lemma weightOrderedRemainder_threshold_sum {n : ℕ} (P : Model.Instance n)
    (wgt : ℝ →ᵇ ℝ) (N : ℕ) {d : ℝ} (hd : 0≤d) :
    (∑ i, thresholdMarkIntensity ((weightOrderedRemainder P wgt N).law i) d)=
      weightOrderedBandResidual P wgt N d := by
  rw [← weightOrderedRemainder_band_sum P wgt N hd]
  apply Finset.sum_congr rfl
  intro i _
  apply FiniteMeasure.toMeasure_injective
  rfl

lemma OrderedBandConvergence.prefix_marginal_tendsto
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (K : ℕ) (i : Fin K) :
    Tendsto (fun m => (weightOrderedPrefix (P m) wgt K).marginalProbabilityLaw i)
      atTop (𝓝 ((B.individualPrefix K).marginalProbabilityLaw i)) := by
  exact h.individual_weak i.val

theorem OrderedBandConvergence.residual_evaluation_inputs
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (d : ℝ) (hd : 0<d) (_hAtom : B.intensity {d}=0)
    (hWeak : Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d)
      atTop (𝓝 (B.intensityAbove d (by simpa [hZero] using hd)))) :
    Tendsto (fun m => ∑ i, thresholdMarkIntensity ((weightOrderedRemainder (P m) wgt (Ns m)).law i) d)
        atTop (𝓝 (B.intensityAbove d (by simpa [hZero] using hd))) ∧
      (∃ L : ℝ, 0≤L ∧ ∀ m, (weightOrderedRemainder (P m) wgt (Ns m)).tailCount d≤L) ∧
      Tendsto (fun m => residualTailSup (fun j => weightOrderedPaddedLaw (P m) wgt j) (Ns m) d)
        atTop (𝓝 (0:ℝ)) := by
  have hAbove : (B.terminal:ℝ)<d := by simpa [hZero] using hd
  refine ⟨?_,?_,h.residualTailSup_tendsto_zero Ns hNs d hAbove⟩
  · simpa only [weightOrderedRemainder_threshold_sum _ _ _ hd.le] using hWeak
  · obtain ⟨L,hL,hTail⟩ := h.above_reserve d hAbove
    exact ⟨L,hL,fun m => (weightOrderedRemainder_tailCount_le (P m) wgt (Ns m) hd.le).trans (hTail m)⟩
end ProphetSecretary.Limiting
