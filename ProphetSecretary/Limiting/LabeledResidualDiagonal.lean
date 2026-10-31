import ProphetSecretary.Limiting.LabeledBandConvergence
import ProphetSecretary.Limiting.SlowFiniteMeasureDiagonal
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs
import ProphetSecretary.Limiting.OrderedResidualRestriction
import ProphetSecretary.Probability.WeakFiniteUpperRestriction

/-!
# One residual diagonal for arbitrary chosen labels

The diagonal is selected from the source's two ordered weak limits. Exact
upper restriction extends its countable cutoff limits to every Poisson
continuity level; residual rarity retains the same original coordinates.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting

lemma labeledBandResidual_restrict {n : ℕ} (P : Model.Instance n) (N : ℕ) {d b : ℝ} (hdb : d≤b) :
    (labeledBandResidual P N d).restrict (Ioi b)=labeledBandResidual P N b := by
  unfold labeledBandResidual
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.restrict_measure_eq,FiniteMeasure.toMeasure_sum,FiniteMeasure.toMeasure_sum]
  ext S hS
  rw [Measure.restrict_apply hS]
  simp only [Measure.coe_finsetSum,Finset.sum_apply,FiniteMeasure.restrict_measure_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply (hS.inter measurableSet_Ioi),Measure.restrict_apply hS]
  congr 1
  rw [inter_assoc,Ioi_inter_Ioi,max_eq_left hdb]

theorem LabeledBandConvergence.exists_all_continuity_residual_diagonal {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      (∀ (d : ℝ) (hd : (B.terminal : ℝ)<d), B.intensity {d}=0 →
        Tendsto (fun m => labeledBandResidual (P m) (Ns m) d) atTop (𝓝 (B.intensityAbove d hd))) ∧
      ∀ (d : ℝ), (B.terminal : ℝ)<d → ∀ ε>(0 : ℝ),
        ∀ᶠ m in atTop, ∀ i, Ns m≤ i → (labeledPaddedLaw (P m) i : Measure ℝ).real (Ioi d)<ε := by
  obtain ⟨b,_hAnti,hRange,hLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
  let hb := fun j => (hRange j).1
  choose μs hFirst hSecond using (fun j => h.residual_bands (b j) (hb j) (hAtoms j).2 (hAtoms j).1)
  obtain ⟨Ns,hMono,hLe,hTop,hDiag⟩ := exists_slow_finiteMeasure_diagonal
    (fun N m j => labeledBandResidual (P m) N (b j)) (fun N j => μs j N)
    (fun j => B.intensityAbove (b j) (hb j)) (fun N j => hFirst j N) hSecond
  refine ⟨Ns,hMono,hLe,hTop,?_,?_⟩
  · intro d hd hAtom
    obtain ⟨j,hj⟩ := (hLim.eventually (Iio_mem_nhds hd)).exists
    have hAtomLow : (B.intensityAbove (b j) (hb j) : Measure ℝ) {d}=0 := by
      change B.intensity.restrict (Ioi (b j)) {d}=0
      exact le_antisymm ((Measure.restrict_le_self _).trans_eq hAtom) bot_le
    have hRestr := ProphetSecretary.Probability.finite_upperRestriction_tendsto (hDiag j) d hAtomLow
    have hFun : (fun m => (labeledBandResidual (P m) (Ns m) (b j)).restrict (Ioi d))=
        fun m => labeledBandResidual (P m) (Ns m) d :=
      funext (fun m => labeledBandResidual_restrict (P m) (Ns m) hj.le)
    rw [hFun,B.intensityAbove_restrict (hb j) hd hj.le] at hRestr
    exact hRestr
  · intro d hd ε hε
    obtain ⟨N,hRare⟩ := h.rare d hd ε hε
    filter_upwards [hTop (eventually_ge_atTop N),hRare] with m hm hR i hi
    exact hR i (hm.trans hi)

end ProphetSecretary.Limiting
