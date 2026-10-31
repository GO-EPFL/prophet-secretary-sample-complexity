import ProphetSecretary.Limiting.BernoulliPremium
import ProphetSecretary.Limiting.IndividualPotentialDrift

/-!
# Child-to-current premium error along the actual clocks

Replacing a candidate clock affects only its own unseen status. Erasing that
identity therefore recovers exactly the child of the current unseen state.
The finite Bernoulli deletion estimate then gives a quadratic rare-probability
premium error at every elapsed time.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ}

lemma unseen_updated_clock_erase (u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (Model.unseen (Model.history Finset.univ (fun _ => 0) (Function.update u i t) t)).erase i =
      (Model.unseen (Model.history Finset.univ (fun _ => 0) u t)).erase i := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp only [Finset.mem_erase, hj, ne_eq, not_false_eq_true, true_and, Model.unseen,
      Finset.mem_filter, Finset.mem_univ, Model.history, Function.update_of_ne hj]

lemma bernoulli_clock_weighted_child_premium_gap (P : Model.Instance n)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x)
    (p : unitInterval) (k : ℕ) (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (u : Fin (n + k) → ℝ) (t : ℝ) (j : Fin k) :
    let Q := finitePoissonDesign P κ hκ p k
    let child := Q.continuationAtArrival w c (fun _ => 0) (Function.update u (j.natAdd n) t) (j.natAdd n)
    let current := poissonContinuation Q w c u t
    0 ≤ (p : ℝ) * (Model.positivePremium κ w child - Model.positivePremium κ w current) ∧
      (p : ℝ) * (Model.positivePremium κ w child - Model.positivePremium κ w current) ≤
        w * (p : ℝ) ^ 2 * ∫ x, x ∂κ := by
  let A := Model.unseen (Model.history Finset.univ (fun _ => 0) u t)
  have h := finitePoissonDesign_weighted_child_premium_gap P κ hκ p k hP hI A j hw
    (mul_nonneg hc (le_max_left 0 (1 - t)))
  dsimp only at h ⊢
  unfold Model.Instance.continuationAtArrival
  rw [Function.update_self, unseen_updated_clock_erase]
  exact h

end ProphetSecretary.Limiting
