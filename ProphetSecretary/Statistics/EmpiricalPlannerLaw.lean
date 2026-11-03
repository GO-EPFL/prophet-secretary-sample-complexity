import ProphetSecretary.Statistics.EmpiricalPlannerData
import ProphetSecretary.Model.Empirical
import ProphetSecretary.Model.BellmanResidualBasic

/-!
# Stored empirical computations and their distributional meaning

The computed positive probability is the actual mass above zero. Factoring
it out of the empirical Bellman premium gives the planner's conditional
positive-excess callback, including zero-probability marginals.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {m : ℕ} [NeZero m]

lemma empiricalLaw_positiveProbability (y : Fin m → ℝ) :
    (empiricalLaw y).real (Ioi 0) = empiricalPositiveProbability y := by
  have he := integral_empiricalLaw y ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ioi] at he
  simpa [empiricalPositiveProbability, positiveObservations, Set.indicator_apply,
    Finset.sum_boole, smul_eq_mul, div_eq_mul_inv, mul_comm] using he

lemma positivePremium_empiricalLaw_factor (y : Fin m → ℝ) {v : ℝ} (hv : 0 ≤ v) :
    positivePremium (empiricalLaw y) 1 v =
      empiricalPositiveProbability y * empiricalConditionalExcess y v := by
  rw [positivePremium, integral_empiricalLaw, empiricalPositiveProbability_mul_excess y hv]
  simp only [mul_one, max_comm, div_eq_mul_inv, mul_comm]

omit [NeZero m] in
lemma measurable_empiricalPositiveProbability :
    Measurable (fun y : Fin m → ℝ => empiricalPositiveProbability y) := by
  have he : (fun y : Fin m → ℝ => empiricalPositiveProbability y) =
      (fun y => (m : ℝ)⁻¹ * ∑ j : Fin m, if 0 < y j then (1 : ℝ) else 0) := by
    funext y
    simp [empiricalPositiveProbability, positiveObservations, Finset.sum_boole, div_eq_mul_inv, mul_comm]
  rw [he]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
    measurable_const measurable_const

omit [NeZero m] in
lemma measurable_empiricalConditionalExcess :
    Measurable (fun p : (Fin m → ℝ) × ℝ => empiricalConditionalExcess p.1 p.2) := by
  have hy (j : Fin m) : Measurable (fun p : (Fin m → ℝ) × ℝ => p.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hn : Measurable (fun p : (Fin m → ℝ) × ℝ =>
      ∑ j : Fin m, if 0 < p.1 j then max 0 (p.1 j - p.2) else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_lt measurable_const (hy j))
      (measurable_const.max ((hy j).sub measurable_snd)) measurable_const
  have hd : Measurable (fun p : (Fin m → ℝ) × ℝ =>
      ∑ j : Fin m, if 0 < p.1 j then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_lt measurable_const (hy j)) measurable_const measurable_const
  convert hn.div hd using 1
  funext p
  simp [empiricalConditionalExcess, positiveObservations, Finset.sum_filter, Finset.sum_boole]

end ProphetSecretary.Statistics
