import ProphetSecretary.Limiting.OrderedResidualEvaluationInputs

/-!
# A single slow residual schedule with globally bounded cloud scores

Raising the residual prefix by one fixed integer makes every scored band
probability at most one half on every finite index. Cofinality implies that
this changes only finitely many indices of the existing slow schedule, so
all positive continuity-band weak limits are preserved.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology
namespace ProphetSecretary.Limiting

theorem OrderedBandConvergence.exists_cloud_score_diagonal
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (b : ℝ) (hb : (B.terminal:ℝ)<b) :
    ∃ Ns : ℕ → ℕ, Tendsto Ns atTop atTop ∧
      (∀ (d : ℝ) (hd : (B.terminal:ℝ)<d), B.intensity {d}=0 →
        Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d) atTop
          (𝓝 (B.intensityAbove d hd))) ∧
      (∀ m, residualTailSup (fun j => weightOrderedPaddedLaw (P m) wgt j) (Ns m) b≤1/2) ∧
      ∀ m i, ((weightOrderedRemainder (P m) wgt (Ns m)).law i).real (Ioi b)≤1/2 := by
  obtain ⟨Ns,_hMono,_hLe,hTop,hWeak,_hRare⟩ := h.exists_all_continuity_residual_diagonal
  obtain ⟨N,hN⟩ := h.uniformly_rare b hb (1/2) (by norm_num)
  let Ms := fun m => max N (Ns m)
  have hEq : Ms=ᶠ[atTop] Ns := by
    filter_upwards [hTop (eventually_ge_atTop N)] with m hm
    exact max_eq_right hm
  refine ⟨Ms,hTop.congr' hEq.symm,?_,?_,?_⟩
  · intro d hd hAtom
    exact (hWeak d hd hAtom).congr' (hEq.symm.mono (fun m hm => congrArg (fun j => weightOrderedBandResidual (P m) wgt j d) hm))
  · intro m
    exact residualTailSup_le _ _ _ _ (fun j hj => (hN m j ((le_max_left N (Ns m)).trans hj)).le)
  · intro m i
    have hNi : N≤Ms m+i.val := (le_max_left N (Ns m)).trans (Nat.le_add_right _ _)
    exact (hN m (Ms m+i.val) hNi).le
end ProphetSecretary.Limiting
