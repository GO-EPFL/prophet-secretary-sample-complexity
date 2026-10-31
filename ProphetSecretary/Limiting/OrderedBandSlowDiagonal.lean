import ProphetSecretary.Limiting.OrderedBandConvergence
import ProphetSecretary.Limiting.SlowFiniteMeasureDiagonal

/-!
# One actual residual-prefix schedule for countably many continuity cutoffs

The fixed-prefix sequence limit is taken before the residual-prefix limit.
The slow diagonal preserves every chosen weak positive-band limit and makes
every residual individual uniformly rare at every fixed level above reserve.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical
namespace ProphetSecretary.Limiting

theorem OrderedBandConvergence.exists_residual_slow_diagonal
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (b : ℕ → ℝ)
    (hb : ∀ j, (B.terminal:ℝ)<b j)
    (hiAtom : ∀ j i, (B.individuals i:Measure ℝ) {b j}=0) (hμAtom : ∀ j, B.intensity {b j}=0) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m ≤ m) ∧ Tendsto Ns atTop atTop ∧
      (∀ j, Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) (b j)) atTop
        (𝓝 (B.intensityAbove (b j) (hb j)))) ∧
      ∀ (d : ℝ), (B.terminal : ℝ) < d → ∀ ε > 0,
        ∀ᶠ m in atTop, ∀ i, Ns m ≤ i → (weightOrderedPaddedLaw (P m) wgt i:Measure ℝ).real (Ioi d) < ε := by
  choose μs hFirst hSecond using (fun j => h.residual_bands (b j) (hb j) (hiAtom j) (hμAtom j))
  obtain ⟨Ns,hMono,hLe,hTop,hDiag⟩ := exists_slow_finiteMeasure_diagonal
    (fun N m j => weightOrderedBandResidual (P m) wgt N (b j))
    (fun N j => μs j N) (fun j => B.intensityAbove (b j) (hb j))
    (fun N j => hFirst j N) hSecond
  refine ⟨Ns,hMono,hLe,hTop,hDiag,?_⟩
  intro d hd ε hε
  obtain ⟨N,hN⟩ := h.uniformly_rare d hd ε hε
  filter_upwards [hTop (eventually_ge_atTop N)] with m hm
  intro i hi
  exact hN m i (hm.trans hi)
end ProphetSecretary.Limiting
