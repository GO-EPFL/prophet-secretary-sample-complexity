import ProphetSecretary.Limiting.FiniteArrayEvaluation

/-!
# Appending two independent finite families

The marginal laws are concatenated and the resulting instance uses their
actual finite product law. This representation separates retained and replaced
offers without changing either policy class or requiring finite-support laws.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n m : ℕ}

noncomputable def Instance.appendIndependent (P : Instance n) (R : Instance m) : Instance (n + m) where
  law := Fin.addCases P.law R.law
  probability i := by
    induction i using Fin.addCases with
    | left i => simpa only [Fin.addCases_left] using P.probability i
    | right j => simpa only [Fin.addCases_right] using R.probability j
  nonnegative i := by
    induction i using Fin.addCases with
    | left i => simpa only [Fin.addCases_left] using P.nonnegative i
    | right j => simpa only [Fin.addCases_right] using R.nonnegative j

lemma Instance.appendIndependent_law_left (P : Instance n) (R : Instance m) (i : Fin n) :
    (P.appendIndependent R).law (i.castAdd m) = P.law i := by
  simp only [Instance.appendIndependent, Fin.addCases_left]

lemma Instance.appendIndependent_law_right (P : Instance n) (R : Instance m) (j : Fin m) :
    (P.appendIndependent R).law (j.natAdd n) = R.law j := by
  simp only [Instance.appendIndependent, Fin.addCases_right]

lemma Instance.appendIndependent_integrable_maximum (P : Instance n) (R : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) (hR : Integrable Instance.maximum R.valuesLaw) :
    Integrable Instance.maximum (P.appendIndependent R).valuesLaw := by
  apply Instance.integrable_maximum
  intro i
  induction i using Fin.addCases with
  | left i => rw [P.appendIndependent_law_left R i]; exact P.integrable_maximum_iff.mp hP i
  | right j => rw [P.appendIndependent_law_right R j]; exact R.integrable_maximum_iff.mp hR j

lemma Instance.appendIndependent_bounded (P : Instance n) (R : Instance m) {H : ℝ}
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(P.appendIndependent R).law i, x ≤ H := by
  intro i
  induction i using Fin.addCases with
  | left i => rw [P.appendIndependent_law_left R i]; exact hP i
  | right j => rw [P.appendIndependent_law_right R j]; exact hR j

end ProphetSecretary.Model
