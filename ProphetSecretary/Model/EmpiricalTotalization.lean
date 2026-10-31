import ProphetSecretary.Model.Empirical
import ProphetSecretary.Model.Continuation

/-!
# Total empirical instances

Negative entries are clamped only to define an instance on every training outcome.
Independent samples from the manuscript's nonnegative laws are unchanged almost surely.
The empirical law and its integrals are still literal finite sample averages.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

/-- A total nonnegative version of a finite training array. -/
def nonnegativeReservoir {n k : ℕ} (y : Reservoir n k) : Reservoir n k :=
  fun i j => max 0 (y i j)

lemma nonnegativeReservoir_nonnegative {n k : ℕ} (y : Reservoir n k) (i : Fin n) (j : Fin k) :
    0 ≤ nonnegativeReservoir y i j := le_max_left _ _

lemma nonnegativeReservoir_eq {n k : ℕ} (y : Reservoir n k) (hy : ∀ i j, 0 ≤ y i j) :
    nonnegativeReservoir y = y := by
  funext i j
  exact max_eq_right (hy i j)

lemma measurable_nonnegativeReservoir {n k : ℕ} : Measurable (@nonnegativeReservoir n k) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_const.max ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma Instance.reservoir_nonnegative {n : ℕ} (P : Instance n) (k : ℕ) :
    ∀ᵐ y ∂P.reservoirLaw k, ∀ i j, 0 ≤ y i j := by
  simp only [ae_all_iff]
  intro i j
  exact (P.reservoir_coordinate_measurePreserving k i j).quasiMeasurePreserving.ae (P.nonnegative i)

lemma Instance.nonnegativeReservoir_eq_ae {n : ℕ} (P : Instance n) (k : ℕ) :
    nonnegativeReservoir =ᵐ[P.reservoirLaw k] id := by
  filter_upwards [P.reservoir_nonnegative k] with y hy
  exact nonnegativeReservoir_eq y hy

lemma nonnegativeReservoir_le {n k : ℕ} (y : Reservoir n k) {H : ℝ}
    (hH : 0 ≤ H) (hy : ∀ i j, y i j ≤ H) : ∀ i j, nonnegativeReservoir y i j ≤ H :=
  fun i j => max_le hH (hy i j)

/-- The empirical instance is defined for every real array, including null training
outcomes. No proof of nonnegativity is an input to the learner. -/
noncomputable def totalEmpiricalInstance {n k : ℕ} [NeZero k] (y : Reservoir n k) : Instance n :=
  empiricalInstance (nonnegativeReservoir y) (nonnegativeReservoir_nonnegative y)

lemma totalEmpiricalInstance_integrable {n k : ℕ} [NeZero k] (y : Reservoir n k) :
    Integrable Instance.maximum (totalEmpiricalInstance y).valuesLaw :=
  empiricalInstance_integrable (nonnegativeReservoir y) (nonnegativeReservoir_nonnegative y)

lemma totalEmpiricalInstance_eq {n k : ℕ} [NeZero k] (y : Reservoir n k)
    (hy : ∀ i j, 0 ≤ y i j) : totalEmpiricalInstance y = empiricalInstance y hy := by
  apply Instance.eq_of_law_eq
  funext i
  change empiricalLaw (nonnegativeReservoir y i) = empiricalLaw (y i)
  rw [nonnegativeReservoir_eq y hy]

lemma totalEmpiricalInstance_restrictTo {n k : ℕ} [NeZero k] (y : Reservoir n k)
    (A : Finset (Fin n)) :
    (totalEmpiricalInstance y).restrictTo A =
      totalEmpiricalInstance (fun i j => y (stateEmbedding A i) j) := by
  apply Instance.eq_of_law_eq
  rfl

lemma totalEmpiricalInstance_integral {n k : ℕ} [NeZero k] (y : Reservoir n k)
    (i : Fin n) (f : ℝ → ℝ) :
    (∫ x, f x ∂(totalEmpiricalInstance y).law i) =
      (k : ℝ)⁻¹ * ∑ j : Fin k, f (max 0 (y i j)) :=
  integral_empiricalLaw _ f

lemma totalEmpiricalInstance_bounded {n k : ℕ} [NeZero k] (y : Reservoir n k)
    {H : ℝ} (hH : 0 ≤ H) (hy : ∀ i j, y i j ≤ H) (i : Fin n) :
    ∀ᵐ x ∂(totalEmpiricalInstance y).law i, x ≤ H := by
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro j _
  simpa using nonnegativeReservoir_le y hH hy i j

end ProphetSecretary.Model
