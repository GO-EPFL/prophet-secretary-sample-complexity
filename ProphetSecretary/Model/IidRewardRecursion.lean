import ProphetSecretary.Model.ContinuationODE
import ProphetSecretary.Model.StopLossStability

/-! # Exact reward recursions for identical offers and a deterministic standby
The marginal law is fixed while the number of remaining offers decreases. The
recurrences optimize over the full randomized history-dependent policy class;
they follow from the already proved first-arrival Bellman equation.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma Instance.firstChildTimeLaw_mass (i : Fin (n + 1)) :
    (firstChildTimeLaw i).real univ = 1 / ((n : ℝ) + 1) := by
  have hLaw (j : Fin (n + 1)) : firstChildTimeLaw j = firstChildTimeLaw i := by
    unfold firstChildTimeLaw
    rw [Instance.remainingSet_card_eq, Instance.remainingSet_card_eq]
  have hSum := firstChildTimeLaws_totalMass n
  simp_rw [hLaw] at hSum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hSum
  apply (eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0)).2
  nlinarith

lemma stateEmbedding_remaining_eq_succAbove (i : Fin (n + 1)) (j : Fin (remainingSet i).card) :
    stateEmbedding (remainingSet i) j = i.succAbove (Fin.cast (Instance.remainingSet_card_eq i) j) := by
  have hSet : remainingSet i = ({i}ᶜ : Finset (Fin (n + 1))) := by
    ext k
    simp [remainingSet]
  have hCard : ({i}ᶜ : Finset (Fin (n + 1))).card = (remainingSet i).card := by rw [← hSet]
  have h := Finset.orderEmbOfFin_compl_singleton_apply (i := i) hCard j
  change ((remainingSet i).orderEmbOfFin rfl) j = _
  simpa only [← hSet] using h

lemma Instance.optimalReward_sortedChild (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) (i : Fin (n + 1)) :
    optimalScalarValue (P.restrictTo (remainingSet i)) 1 0 = optimalScalarValue (P.child i) 1 0 := by
  apply Instance.optimalScalarValue_eq_of_law_equiv (P.child i) (P.restrictTo (remainingSet i))
    (finCongr (Instance.remainingSet_card_eq i))
    (fun j ↦ by change P.law (stateEmbedding (remainingSet i) j) = P.law (i.succAbove (Fin.cast (Instance.remainingSet_card_eq i) j)); rw [stateEmbedding_remaining_eq_succAbove])
    (P.restrictBy_integrable_maximum (Fin.succAboveEmb i) hP) zero_le_one le_rfl

/-- Exact unrestricted Bellman equation when only reward is scored. -/
theorem Instance.optimalReward_bellman (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) :
    optimalScalarValue P 1 0 =
      (∑ i : Fin (n + 1), ∫ x, max x (optimalScalarValue (P.child i) 1 0) ∂P.law i) / ((n : ℝ) + 1) := by
  rw [P.optimalScalarValue_eq_bellmanValue hP zero_lt_one le_rfl]
  have heach (i : Fin (n + 1)) :
      (∫ z, P.bellmanFirstPayoff i 1 0 z ∂(firstChildTimeLaw i).prod (P.law i)) =
        (1 / ((n : ℝ) + 1)) * ∫ x, max x (optimalScalarValue (P.child i) 1 0) ∂P.law i := by
    have he : P.bellmanFirstPayoff i 1 0 =
        (fun z : ℝ × ℝ ↦ max z.2 (optimalScalarValue (P.child i) 1 0)) := by
      funext z
      simp only [bellmanFirstPayoff, zero_mul, zero_add, one_mul,
        bellmanContinuation, P.optimalReward_sortedChild hP i]
    rw [he]
    have hi : Integrable (fun x : ℝ ↦ max x (optimalScalarValue (P.child i) 1 0)) (P.law i) :=
      (P.integrable_maximum_iff.mp hP i).sup (integrable_const _)
    rw [integral_prod _ (hi.comp_snd (firstChildTimeLaw i))]
    change (∫ _t : ℝ, (∫ x, max x (optimalScalarValue (P.child i) 1 0) ∂P.law i) ∂firstChildTimeLaw i) = _
    rw [integral_const]
    simp only [smul_eq_mul, firstChildTimeLaw_mass]
  unfold bellmanValue
  simp_rw [heach]
  rw [← Finset.mul_sum]
  ring

end ProphetSecretary.Model
