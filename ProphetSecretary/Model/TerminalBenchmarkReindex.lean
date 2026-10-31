import ProphetSecretary.Model.TerminalBenchmark
import ProphetSecretary.Model.Reindex
import ProphetSecretary.Model.ZeroVariableValue
import ProphetSecretary.Model.ExcessMeasure

/-!
# Prophet benchmarks under actual relabeling and independent zero padding

The finite marginal product laws are transported through the relabeling. The
terminal benchmark is then handled by its exact excess-offer identity.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n m : ℕ}

lemma Instance.expectedMaximum_restrictBy_equiv (P : Instance n) (e : Fin m ≃ Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    (P.restrictBy e.toEmbedding).expectedMaximum = P.expectedMaximum := by
  have hForward := P.restrictBy_expectedMaximum_le e.toEmbedding hP
  have hBackward := (P.restrictBy e.toEmbedding).restrictBy_expectedMaximum_le e.symm.toEmbedding
    (P.restrictBy_integrable_maximum e.toEmbedding hP)
  rw [P.restrictBy_equiv_inverse e] at hBackward
  exact le_antisymm hForward hBackward

lemma Instance.expectedMaximum_eq_of_law_equiv (P : Instance n) (Q : Instance m)
    (e : Fin m ≃ Fin n) (he : ∀ i, Q.law i = P.law (e i))
    (hP : Integrable Instance.maximum P.valuesLaw) : Q.expectedMaximum = P.expectedMaximum := by
  have hQ : Q = P.restrictBy e.toEmbedding := Instance.eq_of_law_eq (funext he)
  rw [hQ]
  exact P.expectedMaximum_restrictBy_equiv e hP

lemma Instance.expectedTerminalMaximum_eq_of_law_equiv (P : Instance n) (Q : Instance m)
    (e : Fin m ≃ Fin n) (he : ∀ i, Q.law i = P.law (e i))
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    Q.expectedTerminalMaximum a = P.expectedTerminalMaximum a := by
  have hQP : Q = P.restrictBy e.toEmbedding := Instance.eq_of_law_eq (funext he)
  have hQ : Integrable Instance.maximum Q.valuesLaw := hQP.symm ▸ P.restrictBy_integrable_maximum e.toEmbedding hP
  have hlaw (i : Fin m) : (Q.excessOffers a).law i = (P.excessOffers a).law (e i) := by
    change (Q.law i).map (excessValueMap a) = (P.law (e i)).map (excessValueMap a)
    rw [he i]
  have hM := (P.excessOffers a).expectedMaximum_eq_of_law_equiv (Q.excessOffers a) e hlaw
    (P.excessOffers_integrable_maximum hP ha)
  rw [Q.expectedTerminalMaximum_eq_excess hQ ha,P.expectedTerminalMaximum_eq_excess hP ha,hM]

lemma Instance.expectedTerminalMaximum_appendZeros (P : Instance n) (N : ℕ)
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    (P.appendZeros N).expectedTerminalMaximum a = P.expectedTerminalMaximum a := by
  rw [(P.appendZeros N).expectedTerminalMaximum_eq_excess (P.appendZeros_integrable_maximum N hP) ha,
    P.expectedTerminalMaximum_eq_excess hP ha,P.excessOffers_appendZeros N ha,
    (P.excessOffers a).appendZeros_expectedMaximum N]

end ProphetSecretary.Model
