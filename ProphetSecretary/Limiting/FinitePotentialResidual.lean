import ProphetSecretary.Limiting.FinitePotentialPolicy
import ProphetSecretary.Limiting.FiniteArrayEvaluation
import ProphetSecretary.Model.BellmanResidual

/-!
# Residuals of a finite potential on hybrid branches

Retained transitions use the same potential with the candidate removed.
An anonymous transition leaves the retained state unchanged and contributes
its expected positive premium with a minus sign. These identities preserve
all zero observations in the actual execution.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n N : ℕ}

lemma retainedSet_unseen_combined (X : Fin (n + N) → ℝ) (x u : Fin n → ℝ)
    (v : Fin N → Point) (t : ℝ) :
    Model.retainedSet N (Model.unseen (Model.history Finset.univ X (combinedClocks u v) t)) =
      Model.unseen (Model.history Finset.univ x u t) := by
  rw [Model.unseen_history_values Finset.univ X (combinedValues x v) (combinedClocks u v) t,
    retainedSet_unseen, retainedHistory_history]

noncomputable def poissonContinuation (Q : Model.Instance n) (w c : ℝ) (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  Q.continuationValue (Model.unseen (Model.history Finset.univ (fun _ => 0) u t)) (max 0 (1 - t)) w c

lemma appended_continuation_individual (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (X : Fin (n + N) → ℝ) (x u : Fin n → ℝ) (v : Fin N → Point) (i : Fin n) :
    (Q.appendZeros N).continuationAtArrival w c X (combinedClocks u v) (i.castAdd N) =
      Q.continuationAtArrival w c x u i := by
  have he : combinedClocks u v (i.castAdd N) = u i := by simp [combinedClocks]
  unfold Model.Instance.continuationAtArrival Model.Instance.continuationValue
  simp only [he]
  rw [Q.optimalScalarValue_appendZeros_restrictTo N _ hQ hw (mul_nonneg hc (le_max_left _ _)),
    retainedSet_erase_individual, retainedSet_unseen_combined X x u v]
  rw [he]

lemma appended_continuation_poisson (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (X : Fin (n + N) → ℝ) (u : Fin n → ℝ) (v : Fin N → Point) (j : Fin N) :
    (Q.appendZeros N).continuationAtArrival w c X (combinedClocks u v) (j.natAdd n) =
      poissonContinuation Q w c u (v j).1 := by
  have he : combinedClocks u v (j.natAdd n) = (v j).1 := by simp [combinedClocks]
  unfold Model.Instance.continuationAtArrival poissonContinuation Model.Instance.continuationValue
  simp only [he]
  rw [Q.optimalScalarValue_appendZeros_restrictTo N _ hQ hw (mul_nonneg hc (le_max_left _ _)),
    retainedSet_erase_poisson, retainedSet_unseen_combined X (fun _ => 0) u v]
  rw [he]

lemma poissonContinuation_nonnegative (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (t : ℝ) : 0 ≤ poissonContinuation Q w c u t :=
  Q.continuationValue_nonnegative hQ _ (le_max_left _ _) hw hc

lemma appended_transitionResidual_individual (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (v : Fin N → Point) (i : Fin n) :
    (Q.appendZeros N).transitionResidual (appendIID P κ hκ N) w c (combinedClocks u v) (i.castAdd N) =
      Q.transitionResidual P w c u i := by
  unfold Model.Instance.transitionResidual Model.Instance.lawResidual
  rw [appended_continuation_individual Q hQ hw hc (fun _ => 0) (fun _ => 0) u v]
  simp only [Model.Instance.appendZeros, appendIID, Fin.addCases_left]

lemma appended_transitionResidual_poisson (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (v : Fin N → Point) (j : Fin N) :
    (Q.appendZeros N).transitionResidual (appendIID P κ hκ N) w c (combinedClocks u v) (j.natAdd n) =
      - Model.positivePremium κ w (poissonContinuation Q w c u (v j).1) := by
  unfold Model.Instance.transitionResidual Model.Instance.lawResidual
  rw [appended_continuation_poisson Q hQ hw hc]
  simp only [Model.Instance.appendZeros, appendIID, Fin.addCases_right]
  have hv := poissonContinuation_nonnegative Q hQ hw hc u (v j).1
  simp [Model.positivePremium, max_eq_right (neg_nonpos.mpr hv)]

end ProphetSecretary.Limiting
