import ProphetSecretary.Model.BoundaryBranches
import ProphetSecretary.Model.DurationLoss

/-!
# Exact finite-state decomposition of conditional regret

The complete clock vector is used only to evaluate an analytical loss integral.
The observer still uses the original history-based canonical policy. Each
positive-level continuation state contributes a moving-root branch; levels
below the reward-only continuation contribute identically zero loss.
-/

open MeasureTheory Set Filter
open scoped Topology Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.saturatedDurationValue_mul_remaining (P : Instance n) {z : ℝ} (hz : 0 ≤ z) (t : ℝ) :
    P.saturatedDurationValue (z * (1 - t)) = optimalScalarValue P 1 (z * max 0 (1 - t)) := by
  unfold Instance.saturatedDurationValue
  rw [mul_max_of_nonneg _ _ hz, mul_zero]

lemma Instance.durationActionLoss_eq_branch (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) (t : ℝ) (A : Finset (Fin n))
    (hA : otherUnseen u i t = A) (hx : optimalScalarValue (P.restrictTo A) 1 0 < x) :
    P.durationActionLoss z z' i x u t = ProphetSecretary.Analysis.branchThresholdLoss
      (P.restrictTo A).saturatedDurationValue
      ((P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) x) z z' t := by
  unfold Instance.durationActionLoss ProphetSecretary.Analysis.branchThresholdLoss
  rw [hA, (P.restrictTo A).saturatedDurationValue_root (P.restrictTo_integrable_maximum A hP) hx,
    (P.restrictTo A).saturatedDurationValue_mul_remaining hz,
    (P.restrictTo A).saturatedDurationValue_mul_remaining hz']
  rfl

lemma Instance.durationActionLoss_eq_zero_of_le_baseline (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 < z) (hz' : 0 ≤ z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) (t : ℝ)
    (hx : x ≤ optimalScalarValue (P.restrictTo (otherUnseen u i t)) 1 0) :
    P.durationActionLoss z z' i x u t = 0 := by
  let Q := P.restrictTo (otherUnseen u i t)
  have hQ := P.restrictTo_integrable_maximum (otherUnseen u i t) hP
  let rem := max 0 (1 - t)
  have hrem : 0 ≤ rem := le_max_left _ _
  have hn : x ≤ optimalScalarValue Q 1 (z' * rem) := hx.trans
    (optimalScalarValue_mono Q hQ zero_le_one le_rfl le_rfl (mul_nonneg hz' hrem))
  unfold Instance.durationActionLoss
  change max x (optimalScalarValue Q 1 (z' * rem)) -
    (if optimalScalarValue Q 1 (z * rem) ≤ x then x else optimalScalarValue Q 1 (z' * rem)) = 0
  rw [max_eq_right hn]
  by_cases hr : rem = 0
  · simp only [hr, mul_zero]
    split_ifs with h
    · exact sub_eq_zero.mpr (le_antisymm h hx)
    · exact sub_self _
  · have hp := mul_pos hz (lt_of_le_of_ne hrem (Ne.symm hr))
    have ho := Q.rewardNormalized_strictMonoOn hQ (le_rfl : (0 : ℝ) ≤ 0) hp.le hp
    rw [if_neg (not_le.mpr (hx.trans_lt ho)), sub_self]

noncomputable def Instance.stateBranchLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n))
    (z z' x t : ℝ) : ℝ :=
  if optimalScalarValue (P.restrictTo A) 1 0 < x then
    ProphetSecretary.Analysis.branchThresholdLoss (P.restrictTo A).saturatedDurationValue
      ((P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) x) z z' t else 0

lemma Instance.durationActionLoss_eq_stateBranchLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 < z) (hz' : 0 ≤ z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) (t : ℝ) :
    P.durationActionLoss z z' i x u t = P.stateBranchLoss hP (otherUnseen u i t) z z' x t := by
  unfold Instance.stateBranchLoss
  split_ifs with hx
  · exact P.durationActionLoss_eq_branch hP hz.le hz' i x u t _ rfl hx
  · exact P.durationActionLoss_eq_zero_of_le_baseline hP hz hz' i x u t (le_of_not_gt hx)

/-- State restriction, pending survival, and the unit interval can be separated
without discarding any observed identity, including a zero-valued arrival. -/
lemma Instance.durationLoss_eq_sum_branches (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n)
    (x u : Fin n → ℝ) (i : Fin n) {z z' : ℝ} (hz : 0 < z) (hz' : 0 ≤ z') (t : ℝ) :
    (if t ∈ Icc (0 : ℝ) 1 ∧ t ≤ π.pendingTime () x u i then
      P.durationActionLoss z z' i (x i) u t else 0) =
    ∑ A : Finset (Fin n), π.branchMultiplier () x u i A t * P.stateBranchLoss hP A z z' (x i) t := by
  rw [Finset.sum_eq_single (otherUnseen u i t)]
  · rw [Policy.branchMultiplier, P.durationActionLoss_eq_stateBranchLoss hP hz hz']
    split_ifs <;> simp_all
  · intro A _hA hne
    have hnot : otherUnseen u i t ≠ A := Ne.symm hne
    simp only [Policy.branchMultiplier, hnot, false_and, and_false, if_false, zero_mul]
  · simp

/-- The canonical old action agrees exactly with its continuation comparison,
so the branch decomposition describes the actual Bellman loss. -/
lemma Instance.valuePolicy_arrivalLoss_eq_durationActionLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z)
    (x u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (P.valuePolicy hP zero_le_one hz).rule.arrivalBellmanLoss P 1 z' () x (Function.update u i t) i =
      P.durationActionLoss z z' i (x i) u t := by
  have ha : ((P.valuePolicy hP zero_le_one hz).rule.action () Finset.univ x (Function.update u i t) i = true) ↔
      P.continuationAtArrival 1 z x (Function.update u i t) i ≤ x i := by
    rw [P.continuationAtArrival_eq_threshold zero_lt_one]
    change Decidable.decide (_ ≤ _) = true ↔ 1 * _ ≤ _
    rw [decide_eq_true_eq, one_mul, Function.update_self]
  unfold Policy.arrivalBellmanLoss
  simp only [Function.update_self, one_mul, ha, Instance.continuationAtArrival,
    unseen_replaceClock_erase, Instance.durationActionLoss]

end ProphetSecretary.Model
