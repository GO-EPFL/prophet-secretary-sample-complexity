import ProphetSecretary.Limiting.CountableMeanPrefixMaximum
import ProphetSecretary.Limiting.CountableTruncationLower
import ProphetSecretary.Limiting.IgnorePoisson
import ProphetSecretary.Model.SingleIdentityAfter

/-!
# A timed known-offer lower bound inside a contracted prefix

Choose an identity attaining the largest deterministic prefix mean and
accept it only after time `1-C`. Its actual finite-policy scalar guarantee
extends while ignoring the Poisson cloud and then to the full countable
instance. The optimizer remains the unrestricted full-policy supremum.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem meanPrefix_knownOffer_lower (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (hIndividual : B.AllIndividualDurationScoresZero w c) (hBand : B.AllPositiveBandDurationScoresZero w c)
    (N : ℕ) (hN : 0<N) :
    w*optimalCompetitiveRatio*B.meanPrefixMaximum N+c*(1-optimalCompetitiveRatio^2/2) ≤
      B.optimalScalarValue w c := by
  let Q := B.meanContractPrefix N
  let P := Q.individualPrefix N
  let D := Q.truncation N (Q.markCutoff N) (Q.terminal_lt_markCutoff N)
  have hMean := B.meanContractPrefix_preserves_zero_response_criticality hw hc hCritical hIndividual hBand N
  have hTerminal := Q.terminal_eq_zero_of_critical hw hc.le hMean.1
  obtain ⟨i,hMax⟩ := B.exists_meanPrefix_maximizer hN
  have hXi : P.law i=Measure.dirac (B.individualMean i.val) := B.meanContractPrefix_contracted_laws N i.val i.isLt
  have hP : Integrable Model.Instance.maximum P.valuesLaw := P.integrable_maximum_of_bounded
    (fun j => (Q.individual_supported j.val).mono (fun _ hx => hx.2))
  have hKnown := P.optimalScalarValue_ge_knownOffer_at_globalRatio hP i hXi hw.le hc.le
  rw [hMax] at hKnown
  have hFinite : Model.optimalScalarValue P w c ≤ D.optimalScalarValue w c := D.finiteValue_le hTerminal w c
  exact hKnown.trans (hFinite.trans ((Q.truncation_value_le N (Q.terminal_lt_markCutoff N) w c).trans_eq hMean.2.2.1))

end ProphetSecretary.Limiting.CountableInstance
