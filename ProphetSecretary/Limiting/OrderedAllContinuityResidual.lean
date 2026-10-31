import ProphetSecretary.Limiting.OrderedCofinalResidual
import ProphetSecretary.Limiting.OrderedResidualRestriction
import ProphetSecretary.Limiting.OrderedResidualTailSup
import ProphetSecretary.Probability.WeakFiniteUpperRestriction

/-!
# One residual diagonal at every positive cloud continuity level

A cofinal countable family of weak band limits extends to any higher cloud
continuity level by exact restriction of measures. The same actual schedule
makes the largest residual individual probability vanish at every fixed
above-reserve level, as used in `updual:scorelift`.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical
namespace ProphetSecretary.Limiting

theorem OrderedBandConvergence.exists_all_continuity_residual_diagonal
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m ≤ m) ∧ Tendsto Ns atTop atTop ∧
      (∀ (d : ℝ) (hd : (B.terminal:ℝ)<d), B.intensity {d}=0 →
        Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d) atTop
          (𝓝 (B.intensityAbove d hd))) ∧
      ∀ (d : ℝ), (B.terminal:ℝ)<d →
        Tendsto (fun m => residualTailSup (fun i => weightOrderedPaddedLaw (P m) wgt i) (Ns m) d)
          atTop (𝓝 (0:ℝ)) := by
  obtain ⟨b,hb,Ns,_hAnti,_hUpper,hLim,_hAtoms,hMono,hLe,hTop,hWeak,_hRare⟩ :=
    h.exists_cofinal_residual_diagonal
  refine ⟨Ns,hMono,hLe,hTop,?_,fun d hd => h.residualTailSup_tendsto_zero Ns hTop d hd⟩
  intro d hd hAtom
  obtain ⟨j,hj⟩ := (hLim.eventually (Iio_mem_nhds hd)).exists
  have hAtomLow : (B.intensityAbove (b j) (hb j):Measure ℝ) {d}=0 := by
    change B.intensity.restrict (Ioi (b j)) {d}=0
    rw [Measure.restrict_apply (measurableSet_singleton d)]
    have hset : ({d}:Set ℝ) ∩ Ioi (b j)={d} := by
      apply inter_eq_left.mpr
      intro x hx
      simpa only [mem_singleton_iff.mp hx,mem_Ioi] using hj
    rw [hset,hAtom]
  have hRestr := ProphetSecretary.Probability.finite_upperRestriction_tendsto (hWeak j) d hAtomLow
  have hFun : (fun m => (weightOrderedBandResidual (P m) wgt (Ns m) (b j)).restrict (Ioi d))=
      (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d) := by
    funext m
    exact weightOrderedBandResidual_restrict (P m) wgt (Ns m) hj.le
  rw [hFun,B.intensityAbove_restrict (hb j) hd hj.le] at hRestr
  exact hRestr
end ProphetSecretary.Limiting
