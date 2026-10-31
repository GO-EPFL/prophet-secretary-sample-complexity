import ProphetSecretary.Model.SurvivalBound
import ProphetSecretary.Model.PendingFirstMoment
import ProphetSecretary.Model.StopLossStability

/-!
# Continuation controlled by the first moment still pending

At a candidate arrival, each other unobserved identity contributes its marginal
mean. Waiting contributes c times the remaining horizon. This upper bound uses
only the unseen identities and their laws; no future values enter the policy.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.totalFirstMoment_restrictTo_eq_sum (P : Instance n) (A : Finset (Fin n)) :
    (P.restrictTo A).totalFirstMoment = ∑ j ∈ A, (∫ x, x ∂P.law j) :=
  sum_stateEmbedding A (fun j => ∫ x, x ∂P.law j)

lemma Instance.unseenFirstMoment_le_pending (P : Instance n) (x u : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    (P.restrictTo ((unseen (history Finset.univ x u t)).erase i)).totalFirstMoment ≤
      P.pendingFirstMoment i t u := by
  rw [P.totalFirstMoment_restrictTo_eq_sum]
  let A := (unseen (history Finset.univ x u t)).erase i
  have hsub : A ⊆ Finset.univ.erase i := fun j hj =>
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩
  have htime (j : Fin n) (hj : j ∈ A) : t ≤ u j := by
    have hu := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
    change (if j ∈ Finset.univ ∧ u j < t then some (u j, x j) else none) = none at hu
    by_contra hn
    simp only [Finset.mem_univ, true_and, not_le.mp hn, if_true] at hu
    contradiction
  calc
    (∑ j ∈ A, ∫ a, a ∂P.law j) =
        ∑ j ∈ A, if t ≤ u j then (∫ a, a ∂P.law j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (if_pos (htime j hj)).symm
    _ ≤ P.pendingFirstMoment i t u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j _ _
      split_ifs
      · exact integral_nonneg_of_ae (P.nonnegative j)
      · exact le_rfl

/-- Continuation bound for a fixed candidate and the actual unseen state. -/
theorem Instance.continuationAtArrival_le_pendingFirstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (i : Fin n) (hu : u i ≤ 1) :
    P.continuationAtArrival w c x u i ≤ w * P.pendingFirstMoment i (u i) u + c * (1 - u i) := by
  let A := (unseen (history Finset.univ x u (u i))).erase i
  have hA := P.restrictTo_integrable_maximum A hP
  have hv := optimalScalarValue_le_benchmark (P.restrictTo A) hA hw
    (mul_nonneg hc (sub_nonneg.mpr hu))
  have hm := (P.restrictTo A).expectedMaximum_le_totalFirstMoment hA
  have hp := P.unseenFirstMoment_le_pending x u i (u i)
  change optimalScalarValue (P.restrictTo A) w (c * max 0 (1 - u i)) ≤ _
  rw [max_eq_right (sub_nonneg.mpr hu)]
  exact hv.trans (add_le_add (mul_le_mul_of_nonneg_left (hm.trans hp) hw) le_rfl)

end ProphetSecretary.Model
