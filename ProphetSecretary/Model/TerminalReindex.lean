import ProphetSecretary.Model.TerminalScalarValue
import ProphetSecretary.Model.TerminalZeroWeight
import ProphetSecretary.Model.Reindex

/-!
# Fixed-terminal values under a relabeling of the finite identities

Excess laws commute with the actual marginal relabeling, so the already proved
full-policy scalar-value transport and exact reserve removal preserve terminal
values. This includes zero reward weight and arbitrary original zero identities.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n m : ℕ}

lemma Instance.optimalTerminalScalarValue_eq_of_law_equiv (P : Instance n) (Q : Instance m)
    (e : Fin m ≃ Fin n) (he : ∀ i, Q.law i = P.law (e i))
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalTerminalScalarValue Q a w c = optimalTerminalScalarValue P a w c := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalTerminalScalarValue_zero_rewardWeight Q a hc,optimalTerminalScalarValue_zero_rewardWeight P a hc]
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hQP : Q = P.restrictBy e.toEmbedding := Instance.eq_of_law_eq (funext he)
    have hQ : Integrable Instance.maximum Q.valuesLaw := hQP.symm ▸ P.restrictBy_integrable_maximum e.toEmbedding hP
    have hlaw (i : Fin m) : (Q.excessOffers a).law i = (P.excessOffers a).law (e i) := by
      change (Q.law i).map (excessValueMap a) = (P.law (e i)).map (excessValueMap a)
      rw [he i]
    have hV := (P.excessOffers a).optimalScalarValue_eq_of_law_equiv (Q.excessOffers a) e hlaw
      (P.excessOffers_integrable_maximum hP ha) hw hc
    calc
      _ = w * a + optimalScalarValue (Q.excessOffers a) w c := optimalTerminalScalarValue_eq_excessValue Q hQ ha hwpos hc
      _ = w * a + optimalScalarValue (P.excessOffers a) w c := congrArg (fun x : ℝ => w * a + x) hV
      _ = _ := (optimalTerminalScalarValue_eq_excessValue P hP ha hwpos hc).symm

end ProphetSecretary.Model
