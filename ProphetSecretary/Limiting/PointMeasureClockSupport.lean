import ProphetSecretary.Limiting.RawFirstPointReward

/-!
# Clock support of an analytical accepted-point measure

Nonnegative time is required only at eligible candidates. No finiteness of the
number of analytical acceptances, or of their total mass, is imposed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.FirstAcceptance

lemma pointMeasure_nonnegative_clocks {Ω : Type*} {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (hu : ∀ i, A ω i → 0 ≤ u ω i) : ∀ᵐ p ∂pointMeasure A u x ω, 0 ≤ p.1 := by
  rw [pointMeasure,Measure.ae_sum_iff]
  intro i
  split_ifs with hi
  · exact (ae_dirac_iff (measurableSet_le measurable_const measurable_fst)).mpr (hu i hi)
  · simp

end ProphetSecretary.Limiting.FirstAcceptance
