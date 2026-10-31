import ProphetSecretary.Limiting.BandGeneratingFunctional
import ProphetSecretary.Limiting.CommonContinuityCutoffs

/-!
# Common continuity cutoffs of an actual countable instance

The cloud intensity is the proved countable sum of finite bands. Its atoms,
together with the countably many retained marginal atoms, form a countable
set. Its dense complement gives cutoffs decreasing strictly to the reserve.
-/
open MeasureTheory Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Limiting

lemma countable_atoms_of_sfinite (μ : Measure ℝ) [SFinite μ] :
    {b : ℝ | 0<μ {b}}.Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := μ) measurable_id
  apply h.mono
  intro b hb
  simpa only [id_eq,setOf_eq_eq_singleton] using hb

theorem CountableInstance.exists_common_continuity_cutoffs (B : CountableInstance) :
    ∃ b : ℕ → ℝ, StrictAnti b ∧ (∀ j, (B.terminal:ℝ)<b j ∧ b j<(B.terminal:ℝ)+1) ∧
      Tendsto b atTop (𝓝 (B.terminal:ℝ)) ∧
      ∀ j, B.intensity {b j}=0 ∧ ∀ i, (B.individuals i:Measure ℝ) {b j}=0 := by
  let A : Set ℝ := {b | 0<B.intensity {b}} ∪ ⋃ i, {b | 0<(B.individuals i:Measure ℝ) {b}}
  have hA : A.Countable := (countable_atoms_of_sfinite B.intensity).union
    (Set.countable_iUnion (fun i => countable_atoms_of_sfinite (B.individuals i:Measure ℝ)))
  have hd : Dense Aᶜ := Set.Countable.dense_compl ℝ hA
  obtain ⟨b,hAnti,hmem,hLim⟩ := hd.exists_seq_strictAnti_tendsto_of_lt
    (show (B.terminal:ℝ)<(B.terminal:ℝ)+1 by linarith)
  refine ⟨b,hAnti,(fun j => (hmem j).1),hLim,?_⟩
  intro j
  constructor
  · apply le_antisymm _ bot_le
    exact not_lt.mp (fun h => (hmem j).2 (Or.inl h))
  · intro i
    apply le_antisymm _ bot_le
    exact not_lt.mp (fun h => (hmem j).2 (Or.inr (mem_iUnion.mpr ⟨i,h⟩)))
end ProphetSecretary.Limiting
