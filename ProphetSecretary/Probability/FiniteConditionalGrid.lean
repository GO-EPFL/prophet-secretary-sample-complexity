import ProphetSecretary.Probability.ConditionalMaximalMoments

/-!
# Conditional-expectation maxima on arbitrary finite time grids

The supplied grid is sorted using its finite order embedding. Conditional
expectations on that sorted grid form an actual martingale. Sorting is purely
analytical and does not change the observation sigma algebras.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Probability

noncomputable def finiteTimeGrid (s : Finset ℝ) (hs : s.Nonempty) (j : ℕ) : ℝ :=
  s.orderEmbOfFin rfl ⟨min j (s.card - 1), by have := hs.card_pos; omega⟩

lemma finiteTimeGrid_monotone (s : Finset ℝ) (hs : s.Nonempty) : Monotone (finiteTimeGrid s hs) := by
  intro j k hjk
  apply (s.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hjk

lemma finiteTimeGrid_mem (s : Finset ℝ) (hs : s.Nonempty) (j : ℕ) : finiteTimeGrid s hs j ∈ s :=
  s.orderEmbOfFin_mem rfl _

lemma finiteTimeGrid_covers (s : Finset ℝ) (hs : s.Nonempty) {t : ℝ} (ht : t ∈ s) :
    ∃ j ≤ s.card - 1, finiteTimeGrid s hs j = t := by
  let k := (s.orderIsoOfFin rfl).symm ⟨t,ht⟩
  refine ⟨k.val, by have := k.isLt; omega, ?_⟩
  have hmin : min k.val (s.card - 1) = k.val := min_eq_left (by have := k.isLt; omega)
  unfold finiteTimeGrid
  simp only [hmin]
  exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨t,ht⟩)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def sampledTimeFiltration (ℱ : Filtration ℝ mΩ) (t : ℕ → ℝ) (ht : Monotone t) : Filtration ℕ mΩ where
  seq j := ℱ (t j)
  mono' _ _ hij := ℱ.mono (ht hij)
  le' j := ℱ.le (t j)

lemma sampledTimeFiltration_apply (ℱ : Filtration ℝ mΩ) (t : ℕ → ℝ) (ht : Monotone t) (j : ℕ) :
    sampledTimeFiltration ℱ t ht j = ℱ (t j) := rfl

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Second moment of the sorted-grid maximum, with no grid-cardinality factor. -/
theorem finiteConditionalGrid_secondMoment (ℱ : Filtration ℝ mΩ) (f : Ω → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D)
    (hf : Integrable (fun ω => ‖f ω‖ ^ 2) μ) (s : Finset ℝ) (hs : s.Nonempty) :
    (∫ ω, runningMaximum (fun j => |μ[f | ℱ (finiteTimeGrid s hs j)] ω|) (s.card - 1) ^ 2 ∂μ) ≤
      4 * ∫ ω, ‖f ω‖ ^ 2 ∂μ :=
  condExp_runningAbsMaximum_secondMoment μ
    (sampledTimeFiltration ℱ _ (finiteTimeGrid_monotone s hs)) f hD hbound hf _

/-- Sixth moment of the same maximum, also uniform over finite grids. -/
theorem finiteConditionalGrid_sixthMoment (ℱ : Filtration ℝ mΩ) (f : Ω → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D)
    (hf : Integrable (fun ω => ‖f ω‖ ^ 6) μ) (s : Finset ℝ) (hs : s.Nonempty) :
    (∫ ω, runningMaximum (fun j => |μ[f | ℱ (finiteTimeGrid s hs j)] ω|) (s.card - 1) ^ 6 ∂μ) ≤
      13 * ∫ ω, ‖f ω‖ ^ 6 ∂μ :=
  condExp_runningAbsMaximum_sixthMoment μ
    (sampledTimeFiltration ℱ _ (finiteTimeGrid_monotone s hs)) f hD hbound hf _

end ProphetSecretary.Probability
