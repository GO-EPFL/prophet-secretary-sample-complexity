import ProphetSecretary.Model.TerminalReindex
import ProphetSecretary.Model.ExcessMeasure
import ProphetSecretary.Model.ZeroVariableValue

/-!
# Fixed terminal rewards under appended zero identities

The causal zero-variable simulator preserves the full observable zero history.
Reserve removal commutes with the actual appended zero laws.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.optimalTerminalScalarValue_appendZeros (P : Instance n) (N : ℕ)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalTerminalScalarValue (P.appendZeros N) a w c = optimalTerminalScalarValue P a w c := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalTerminalScalarValue_zero_rewardWeight _ _ hc,optimalTerminalScalarValue_zero_rewardWeight _ _ hc]
  · have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    rw [optimalTerminalScalarValue_eq_excessValue _ (P.appendZeros_integrable_maximum N hP) ha hwP hc,
      optimalTerminalScalarValue_eq_excessValue P hP ha hwP hc,P.excessOffers_appendZeros N ha,
      (P.excessOffers a).optimalScalarValue_appendZeros N (P.excessOffers_integrable_maximum hP ha) hw hc]

end ProphetSecretary.Model
