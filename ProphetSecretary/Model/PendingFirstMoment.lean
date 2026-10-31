import ProphetSecretary.Stability.TerminalWindow
import ProphetSecretary.Model.TruncatedReward

/-!
# First moment still pending at a fixed elapsed time

The coefficients are marginal means, not future offer values supplied to a
policy. Each other identity remains unseen with probability 1−t. The resulting
expectation bound is uniform in the number of identities and does not require
independence between survival and the set of unseen identities.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.pendingFirstMoment (P : Instance n) (i : Fin n)
    (t : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, if t ≤ u j then (∫ x, x ∂P.law j) else 0

lemma Instance.pendingFirstMoment_nonnegative (P : Instance n) (i : Fin n)
    (t : ℝ) (u : Fin n → ℝ) : 0 ≤ P.pendingFirstMoment i t u := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact integral_nonneg_of_ae (P.nonnegative j)
  · exact le_rfl

lemma Instance.measurable_pendingFirstMoment (P : Instance n) (i : Fin n) (t : ℝ) :
    Measurable (P.pendingFirstMoment i t) := by
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply j))
    measurable_const measurable_const

lemma Instance.integrable_pendingFirstMoment (P : Instance n) (i : Fin n) (t : ℝ) :
    Integrable (P.pendingFirstMoment i t) (Instance.clocksLaw n) := by
  apply integrable_finsetSum
  intro j _
  exact (integrable_const (∫ x, x ∂P.law j)).indicator
    (measurableSet_le measurable_const (measurable_pi_apply j))

/-- The precise clock expectation; the candidate itself is excluded. -/
theorem Instance.integral_pendingFirstMoment (P : Instance n) (i : Fin n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u, P.pendingFirstMoment i t u ∂Instance.clocksLaw n) =
      (1 - t) * ∑ j ∈ Finset.univ.erase i, (∫ x, x ∂P.law j) := by
  have hm (j : Fin n) : MeasurableSet {u : Fin n → ℝ | t ≤ u j} :=
    measurableSet_le measurable_const (measurable_pi_apply j)
  have hi (j : Fin n) : Integrable (fun u : Fin n → ℝ => if t ≤ u j then (∫ x, x ∂P.law j) else 0)
      (Instance.clocksLaw n) :=
    (integrable_const _).indicator (hm j)
  unfold pendingFirstMoment
  rw [integral_finsetSum _ (fun j _ => hi j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hp : MeasurePreserving (fun u : Fin n → ℝ => u j) (Instance.clocksLaw n) Instance.uniformClock :=
    measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) j
  have he := map_measureReal_apply (μ := Instance.clocksLaw n) hp.measurable (s := Ici t) measurableSet_Ici
  rw [hp.map_eq, Instance.uniformClock_probability_ge ht0 ht1] at he
  have hind := integral_indicator_one (μ := Instance.clocksLaw n) (hm j)
  have hprob : (∫ u : Fin n → ℝ, if t ≤ u j then (1 : ℝ) else 0 ∂Instance.clocksLaw n) = 1 - t := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using hind.trans he.symm
  have hfun : (fun u : Fin n → ℝ => if t ≤ u j then (∫ x, x ∂P.law j) else 0) =
      fun u => (∫ x, x ∂P.law j) * (if t ≤ u j then (1 : ℝ) else 0) := by
    funext u
    split_ifs <;> simp
  rw [hfun, integral_const_mul, hprob, mul_comm]

theorem Instance.integral_pendingFirstMoment_le (P : Instance n) (i : Fin n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u, P.pendingFirstMoment i t u ∂Instance.clocksLaw n) ≤ (1 - t) * P.totalFirstMoment := by
  rw [P.integral_pendingFirstMoment i ht0 ht1]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
    (fun j _ _ => integral_nonneg_of_ae (P.nonnegative j))

end ProphetSecretary.Model
