import ProphetSecretary.Limiting.LabeledResidualDiagonal
import ProphetSecretary.Limiting.LabeledResidualConsistency

/-!
# Residual limits ignore cutoff atoms of already retained individuals

A lower common continuity cutoff provides actual weak residual limits. The
successor identities and cloud limit show that the retained-prefix residual
has no atom wherever the remaining individuals and cloud have none. Exact
restriction then gives the original-sequence limit at that level.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting

theorem LabeledBandConvergence.tail_continuity_residual_limits {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B) (K : ℕ) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (hQ : ∀ i, K≤ i → (B.individuals i : Measure ℝ) {b}=0) (hμ : B.intensity {b}=0) :
    ∃ ρ : ℕ → FiniteMeasure ℝ,
      (∀ N, K≤N → Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 (ρ N))) ∧
      Tendsto ρ atTop (𝓝 (B.intensityAbove b hb)) := by
  obtain ⟨ds,_hAnti,hDs,hDsLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
  obtain ⟨j,hj⟩ := (hDsLim.eventually (Iio_mem_nhds hb)).exists
  let d := ds j
  have hd : (B.terminal : ℝ)<d := (hDs j).1
  have hd0 : 0≤d := B.terminal.property.trans hd.le
  obtain ⟨ρ,hFirst,hSecond⟩ := h.residual_bands d hd (hAtoms j).2 (hAtoms j).1
  have hSucc := residual_successor_of_weak_limits hd0 h.individual_weak hFirst (hAtoms j).2
  have hCloudAtom : (B.intensityAbove d hd : Measure ℝ) {b}=0 :=
    le_antisymm ((Measure.restrict_le_self _).trans_eq hμ) bot_le
  have hResidualAtom (N : ℕ) (hKN : K≤N) : (ρ N : Measure ℝ) {b}=0 :=
    residual_atom_zero_of_remaining_atoms_zero hSucc hSecond hCloudAtom N
      (fun i hNi => hQ i (hKN.trans hNi))
  refine ⟨fun N => (ρ N).restrict (Ioi b),?_,?_⟩
  · intro N hKN
    have hWeak := ProphetSecretary.Probability.finite_upperRestriction_tendsto (hFirst N) b (hResidualAtom N hKN)
    have hEq : (fun m => (labeledBandResidual (P m) N d).restrict (Ioi b))=
        fun m => labeledBandResidual (P m) N b :=
      funext (fun m => labeledBandResidual_restrict (P m) N hj.le)
    rwa [hEq] at hWeak
  · have hWeak := ProphetSecretary.Probability.finite_upperRestriction_tendsto hSecond b hCloudAtom
    rwa [B.intensityAbove_restrict hd hb hj.le] at hWeak

end ProphetSecretary.Limiting
