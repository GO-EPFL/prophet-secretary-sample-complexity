import ProphetSecretary.Reach.Dyadic
import ProphetSecretary.Reach.RootBounds
import ProphetSecretary.Probability.EmpiricalLevel

/-!
# Uniform empirical-clock discrepancy

For `N` independent uniform clocks, the expected measurable empirical-CDF discrepancy
is at most `20 / sqrt N`. The constant is universal. The proof combines finite dyadic
chaining, independent centered fourth moments, and explicit geometric-sum arithmetic.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model.Instance

lemma clocks_mem_positive_unitInterval (N : ℕ) :
    ∀ᵐ u ∂clocksLaw N, ∀ i, 0 < u i ∧ u i ≤ 1 := by
  rw [ae_all_iff]
  intro i
  have hn := (measurePreserving_eval (fun _ : Fin N => uniformClock) i).quasiMeasurePreserving.ae
    (uniformClock.ae_ne (0 : ℝ))
  filter_upwards [clocks_mem_unitInterval (n := N), hn] with u hu hne
  exact ⟨lt_of_le_of_ne (hu i).1 (Ne.symm hne), (hu i).2⟩

end ProphetSecretary.Model.Instance

namespace ProphetSecretary.Reach.ZeroReach

open ProphetSecretary.Model.Instance ProphetSecretary.Reach.EmpiricalChaining

/-- Explicit, instance-size independent empirical-clock bound used in `lem:zeros`. -/
theorem expected_uniform_discrepancy_le (N : ℕ) (hN : 0 < N) :
    (∫ z : Fin N → ℝ, discrepancy z ∂clocksLaw N) ≤ 20 / Real.sqrt (N : ℝ) := by
  let r := Real.sqrt (Real.sqrt (N : ℝ))
  let J := Nat.ceil r
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hNp)
  have hrN : r ^ 4 = (N : ℝ) := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (N : ℝ)) ^ 2 := by rw [show r ^ 2 = Real.sqrt (N : ℝ) from Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = N := Real.sq_sqrt hNp.le
  calc
    (∫ z : Fin N → ℝ, discrepancy z ∂clocksLaw N) ≤
        (∑ j ∈ Finset.range J, ∫ z : Fin N → ℝ,
          levelMaximum (fun z => empiricalCDF z) j z ∂clocksLaw N) + 1 / (2 : ℝ) ^ J :=
      integral_discrepancy_le_sum_levels hN (clocksLaw N) (fun i => measurable_pi_apply i)
        (clocks_mem_positive_unitInterval N) J
    _ ≤ (∑ j ∈ Finset.range J, (2 * (7 / 8 : ℝ) ^ j / r ^ 2 + 1 / r ^ 3)) +
        1 / (2 : ℝ) ^ J := by
      apply add_le_add _ le_rfl
      exact Finset.sum_le_sum fun j _ => ProphetSecretary.Probability.expected_empirical_levelMaximum N hN j hr hrN
    _ ≤ 20 / Real.sqrt (N : ℝ) := dyadic_root_cost_le_sqrt N hN

end ProphetSecretary.Reach.ZeroReach
