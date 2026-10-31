import ProphetSecretary.Limiting.OrderedBandSlowDiagonal
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs

/-!
# Constructed cofinal residual diagonal for ordered body convergence

This combines actual common continuity cutoffs with the slow weak-measure
diagonal used in `updual:scorelift`. Every fixed-cutoff sequence limit is
preserved before the cofinal cutoff-removal limit.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical
namespace ProphetSecretary.Limiting

theorem OrderedBandConvergence.exists_cofinal_residual_diagonal
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) :
    ∃ (b : ℕ → ℝ) (hb : ∀ j, (B.terminal:ℝ)<b j) (Ns : ℕ → ℕ),
      StrictAnti b ∧ (∀ j, b j<(B.terminal:ℝ)+1) ∧ Tendsto b atTop (𝓝 (B.terminal:ℝ)) ∧
      (∀ j, B.intensity {b j}=0 ∧ ∀ i, (B.individuals i:Measure ℝ) {b j}=0) ∧
      Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      (∀ j, Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) (b j)) atTop
        (𝓝 (B.intensityAbove (b j) (hb j)))) ∧
      ∀ (d : ℝ), (B.terminal:ℝ)<d → ∀ ε > 0,
        ∀ᶠ m in atTop, ∀ i, Ns m ≤ i → (weightOrderedPaddedLaw (P m) wgt i:Measure ℝ).real (Ioi d)<ε := by
  obtain ⟨b,hAnti,hRange,hLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
  let hb := fun j => (hRange j).1
  obtain ⟨Ns,hMono,hLe,hTop,hWeak,hRare⟩ := h.exists_residual_slow_diagonal b hb
    (fun j => (hAtoms j).2) (fun j => (hAtoms j).1)
  exact ⟨b,hb,Ns,hAnti,(fun j => (hRange j).2),hLim,hAtoms,hMono,hLe,hTop,hWeak,hRare⟩
end ProphetSecretary.Limiting
