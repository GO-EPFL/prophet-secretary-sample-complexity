import ProphetSecretary.Limiting.CommonContinuityCutoffs
import ProphetSecretary.Limiting.ReserveResidualAtoms

/-!
# Countably many common continuity levels decreasing to the reserve

Countability of atoms of the initial finite weighted aggregate supplies actual
strictly decreasing simultaneous continuity cutoffs for every retained law
and the locally finite reserve intensity.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

theorem exists_reserve_common_continuity_cutoffs (a : ℝ) (w : ℝ →ᵇ ℝ)
    (hpos : ∀ x, a < x → 0 < w x) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) :
    ∃ b : ℕ → ℝ, StrictAnti b ∧ (∀ k, a < b k ∧ b k < a+1) ∧ Tendsto b atTop (𝓝 a) ∧
      ∀ k, (ρ 0 : Measure ℝ) {b k} = 0 ∧ (∀ i, (Q i : Measure ℝ) {b k} = 0) ∧
        reserveMarkIntensity (extractedContinuousWeightedResidual w Q ρ) w a {b k} = 0 := by
  let A : Set ℝ := {b | 0 < (ρ 0 : Measure ℝ) {b}}
  have hA : A.Countable := countable_nonzero_atoms (ρ 0)
  have hd : Dense Aᶜ := Set.Countable.dense_compl ℝ hA
  obtain ⟨b,hanti,hmem,hlim⟩ := hd.exists_seq_strictAnti_tendsto_of_lt (show a < a+1 by linarith)
  refine ⟨b,hanti,(fun k => (hmem k).1),hlim,?_⟩
  intro k
  have hatom : (ρ 0 : Measure ℝ) {b k} = 0 := le_antisymm (not_lt.mp (hmem k).2) bot_le
  exact ⟨hatom,continuousWeighted_common_atom_zero_of_initial w Q ρ hρ (hmem k).1.1
    (hpos (b k) (hmem k).1.1) hatom⟩

end ProphetSecretary.Limiting
