import ProphetSecretary.Model.ScalarIntervalMinimizer
import ProphetSecretary.Statistics.FiniteGridResponseLearner
import ProphetSecretary.Model.EmpiricalTotalization

/-!
# An actual measurable pilot weight for the finite-grid game

A compact empirical minimizer is chosen separately for each of the finitely
many possible training arrays. Finite observation lookup makes that choice
measurable, without a measurable-selection assumption. On every off-grid raw
array the pilot returns the interval's lower endpoint. This module has the
finite-grid scope used in the paper's finite minimax argument.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalIntervalMinimizer (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) (y : (Fin n × Fin k) → ℝ) : ℝ :=
  ((totalEmpiricalInstance (reservoirCoordinates.symm y)).normalizedScalarGap_exists_interval_minimizer
    (totalEmpiricalInstance_integrable _) h0 h1 hlohi).choose

lemma empiricalIntervalMinimizer_mem (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) (y : (Fin n × Fin k) → ℝ) :
    empiricalIntervalMinimizer lo hi h0 h1 hlohi y ∈ Icc lo hi :=
  ((totalEmpiricalInstance (reservoirCoordinates.symm y)).normalizedScalarGap_exists_interval_minimizer
    (totalEmpiricalInstance_integrable _) h0 h1 hlohi).choose_spec.1

lemma empiricalIntervalMinimizer_isMin (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) (y : (Fin n × Fin k) → ℝ) (a : ℝ) (ha : a ∈ Icc lo hi) :
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y))
      (empiricalIntervalMinimizer lo hi h0 h1 hlohi y) ≤
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a :=
  ((totalEmpiricalInstance (reservoirCoordinates.symm y)).normalizedScalarGap_exists_interval_minimizer
    (totalEmpiricalInstance_integrable _) h0 h1 hlohi).choose_spec.2 a ha

noncomputable def finiteGridPilotWeight (G : Finset ℝ) (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) : ((Fin n × Fin k) → ℝ) → ℝ :=
  finiteObservationLookup (preliminaryGrid n k G) lo
    (fun y => empiricalIntervalMinimizer lo hi h0 h1 hlohi y.val)

lemma measurable_finiteGridPilotWeight (G : Finset ℝ) (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) :
    Measurable (finiteGridPilotWeight (n := n) (k := k) G lo hi h0 h1 hlohi) :=
  measurable_finiteObservationLookup _ _ _

lemma finiteGridPilotWeight_mem (G : Finset ℝ) (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) (y : (Fin n × Fin k) → ℝ) :
    finiteGridPilotWeight G lo hi h0 h1 hlohi y ∈ Icc lo hi := by
  unfold finiteGridPilotWeight
  by_cases hy : y∈preliminaryGrid n k G
  · rw [finiteObservationLookup_on _ _ _ y hy]
    exact empiricalIntervalMinimizer_mem lo hi h0 h1 hlohi y
  · rw [finiteObservationLookup_off _ _ _ y hy]
    exact ⟨le_rfl,hlohi⟩

lemma finiteGridPilotWeight_isMin_on_grid (G : Finset ℝ) (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) (y : (Fin n × Fin k) → ℝ)
    (hy : y∈preliminaryGrid n k G) (a : ℝ) (ha : a∈Icc lo hi) :
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y))
      (finiteGridPilotWeight G lo hi h0 h1 hlohi y) ≤
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a := by
  unfold finiteGridPilotWeight
  rw [finiteObservationLookup_on _ _ _ y hy]
  exact empiricalIntervalMinimizer_isMin lo hi h0 h1 hlohi y a ha

lemma finiteGridPilotWeight_isMin_ae (P : Instance n) (G : Finset ℝ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (lo hi : ℝ) (h0 : 0 ≤ lo)
    (h1 : hi ≤ 1) (hlohi : lo ≤ hi) (a : ℝ) (ha : a∈Icc lo hi) :
    ∀ᵐ y ∂P.trainingCoordinateLaw k,
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y))
      (finiteGridPilotWeight G lo hi h0 h1 hlohi y) ≤
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a := by
  filter_upwards [trainingCoordinateLaw_grid_support P G k hG] with y hy
  exact finiteGridPilotWeight_isMin_on_grid G lo hi h0 h1 hlohi y hy a ha

end ProphetSecretary.Statistics
