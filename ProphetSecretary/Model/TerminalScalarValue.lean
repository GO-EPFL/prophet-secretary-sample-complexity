import ProphetSecretary.Model.TerminalPullback

/-!
# Exact finite scalar value with a fixed terminal reward

The supremum still ranges over every admissible measurable randomized policy.
A fixed terminal reward a≥0 contributes wa plus the ordinary optimal scalar
value of the excess offers. Both inequalities have complete causal policy and
mapped-Bellman proofs; no inverse sampling kernel is assumed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def terminalScalarValues (P : Instance n) (a w c : ℝ) : Set ℝ :=
  Set.range (fun π : RandomizedPolicy n => π.terminalScalarObjective P a w c)

noncomputable def optimalTerminalScalarValue (P : Instance n) (a w c : ℝ) : ℝ :=
  sSup (terminalScalarValues P a w c)

lemma terminalScalarValues_nonempty (P : Instance n) (a w c : ℝ) : (terminalScalarValues P a w c).Nonempty :=
  ⟨(RandomizedPolicy.waiting n).terminalScalarObjective P a w c, ⟨RandomizedPolicy.waiting n,rfl⟩⟩

lemma terminalScalarValues_bddAbove (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) : BddAbove (terminalScalarValues P a w c) := by
  refine ⟨w * a + optimalScalarValue (P.excessOffers a) w c, ?_⟩
  rintro y ⟨π,rfl⟩
  exact π.terminalScalarObjective_le_excessValue P hP ha hw hc

/-- Exact reserve removal for the full finite policy class. -/
theorem optimalTerminalScalarValue_eq_excessValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    optimalTerminalScalarValue P a w c = w * a + optimalScalarValue (P.excessOffers a) w c := by
  let Q := P.excessOffers a
  have hQ := P.excessOffers_integrable_maximum hP ha
  let πQ := Q.positiveValuePolicy hQ hw.le hc
  let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
  let πP := πQ.pullbackValuesIndexed f (fun _ => measurable_excessValueMap a)
  have hpos : ∀ (r : πQ.Seed) (x u : Fin n → ℝ) (i : Fin n),
      πQ.rule.ActualSelects r Finset.univ x u i → 0 < x i :=
    fun r x u i hi => Q.positiveValueRule_selects_positive w c r x u i hi
  have hrep := πQ.terminalScalarObjective_excessPullback P hP ha hpos w c
  change πP.terminalScalarObjective P a w c = w * a + πQ.scalarObjective Q w c at hrep
  rw [Q.positiveValuePolicy_optimal hQ hw hc] at hrep
  apply le_antisymm
  · apply csSup_le (terminalScalarValues_nonempty P a w c)
    rintro y ⟨π,rfl⟩
    exact π.terminalScalarObjective_le_excessValue P hP ha hw hc
  · rw [← hrep]
    exact le_csSup (terminalScalarValues_bddAbove P hP ha hw hc) ⟨πP,rfl⟩

end ProphetSecretary.Model
