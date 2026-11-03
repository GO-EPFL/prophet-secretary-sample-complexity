import ProphetSecretary.Probability.BernoulliSubset
import ProphetSecretary.Probability.UniformClockReflection
import ProphetSecretary.Model.ScalarBands

/-!
# Integrating the unseen subset at a fixed arrival time

Conditioning a candidate's clock leaves the other independent clocks uniform.
Reflection identifies the unseen identities with a Bernoulli subset whose
inclusion probability is the remaining-time fraction.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

lemma integral_bernoulliSubset_constant {n : ℕ} (A : Finset (Fin n))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (f : Finset (Fin n) → ℝ) :
    (∫ u, f (bernoulliSubset A (fun _ => s) u) ∂Model.Instance.clocksLaw n) =
      ∑ B ∈ A.powerset, s^B.card * (1-s)^(A.card-B.card) * f B := by
  have he (u : Fin n → ℝ) : f (bernoulliSubset A (fun _ => s) u) =
      ∑ B ∈ A.powerset, if bernoulliSubset A (fun _ => s) u = B then f B else 0 := by
    have hm : bernoulliSubset A (fun _ => s) u ∈ A.powerset :=
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    simp [hm]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro B hB
    have hi := integral_indicator_const (μ := Model.Instance.clocksLaw n) (f B)
      (measurableSet_bernoulliSubset_fiber A B (fun _ => s))
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul,
      bernoulliSubset_constant_probability A B hs (Finset.mem_powerset.mp hB)] using hi
  · intro B _
    apply Integrable.of_bound
      (measurable_const.ite (measurableSet_bernoulliSubset_fiber A B (fun _ => s))
        measurable_const).aestronglyMeasurable |f B|
    filter_upwards [] with u
    by_cases hu : bernoulliSubset A (fun _ => s) u = B
    · simp [hu, Real.norm_eq_abs]
    · simp [hu, abs_nonneg]

lemma otherUnseen_reflected_eq_bernoulliSubset {n : ℕ}
    (u : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    Model.otherUnseen (fun j => 1-u j) i (1-s) =
      bernoulliSubset (Finset.univ.erase i) (fun _ => s) u := by
  ext j
  simp only [Model.otherUnseen, bernoulliSubset, Finset.mem_filter]
  constructor
  · rintro ⟨hj, h⟩
    exact ⟨hj, by linarith⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, by linarith⟩

end ProphetSecretary.Probability
