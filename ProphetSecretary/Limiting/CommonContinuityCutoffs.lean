import ProphetSecretary.Limiting.WeightedResidualAtoms
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.IsLUB

/-!
# Actual countable common continuity cutoffs

A finite weighted aggregate has only countably many nonzero atoms. Its null
atoms have dense complement, supplying a strictly decreasing positive cutoff
sequence tending to zero. The proved atom correspondence makes every cutoff
a simultaneous continuity level of all retained marginal laws and the
constructed possibly infinite positive-mark intensity.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

lemma countable_nonzero_atoms (μ : FiniteMeasure ℝ) :
    {b : ℝ | 0 < (μ : Measure ℝ) {b}}.Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := (μ : Measure ℝ)) measurable_id
  apply h.mono
  intro b hb
  have hset : {x : ℝ | id x = b} = {b} := by ext x; simp
  change 0 < (μ : Measure ℝ) {x | id x = b}
  rw [hset]
  exact hb

/-- The cutoff sequence is constructed from actual atom countability, not
included as an unproved field of an extraction structure. -/
theorem exists_positive_continuity_cutoffs (μ : FiniteMeasure ℝ) :
    ∃ b : ℕ → ℝ, StrictAnti b ∧ (∀ k, 0 < b k ∧ b k < 1) ∧ Tendsto b atTop (𝓝 0) ∧
      ∀ k, (μ : Measure ℝ) {b k} = 0 := by
  let A : Set ℝ := {b | 0 < (μ : Measure ℝ) {b}}
  have hA : A.Countable := countable_nonzero_atoms μ
  have hd : Dense Aᶜ := Set.Countable.dense_compl ℝ hA
  obtain ⟨b,hanti,hmem,hlim⟩ := hd.exists_seq_strictAnti_tendsto_of_lt (by norm_num : (0 : ℝ) < 1)
  refine ⟨b,hanti,(fun k => (hmem k).1),hlim,?_⟩
  intro k
  have hn : ¬0 < (μ : Measure ℝ) {b k} := (hmem k).2
  exact le_antisymm (not_lt.mp hn) bot_le

/-- Common positive continuity levels for every retained marginal and the
residual intensity, with the strict ordering and zero limit explicit. -/
theorem exists_extracted_common_continuity_cutoffs (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    ∃ b : ℕ → ℝ, StrictAnti b ∧ (∀ k, 0 < b k ∧ b k < 1) ∧ Tendsto b atTop (𝓝 0) ∧
      ∀ k, (ρ 0 : Measure ℝ) {b k} = 0 ∧
        (∀ i, (Q i : Measure ℝ) {b k} = 0) ∧
        positiveMarkIntensity (extractedWeightedResidual H Q ρ) {b k} = 0 := by
  obtain ⟨b,hanti,hpos,hlim,hatoms⟩ := exists_positive_continuity_cutoffs (ρ 0)
  refine ⟨b,hanti,hpos,hlim,?_⟩
  intro k
  exact ⟨hatoms k,extracted_common_atom_zero_of_initial H Q ρ hρ hQ (hpos k).1 (hatoms k)⟩

end ProphetSecretary.Limiting
