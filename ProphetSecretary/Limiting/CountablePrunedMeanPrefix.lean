import ProphetSecretary.Limiting.CountableMeanContractionPrefix
import ProphetSecretary.Limiting.CountableTailLawEquality
import ProphetSecretary.Limiting.CountableBandValueMinimum
import ProphetSecretary.Limiting.CountableBandBenchmarkDeletion

/-!
# Critical finite-mean prefixes with the high Poisson cloud deleted

For each N independently, first contract the first N individual marginals,
then delete the first N+1 construction bands. Both scalar value and prophet
expectation are preserved by the proved finite operations. This construction
uses no convergence of optimizers, responses, or score expectations.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def prunedMeanPrefix (B : CountableInstance) (N : ℕ) : CountableInstance :=
  (B.meanContractPrefix N).deleteFirstBands N

@[simp] lemma prunedMeanPrefix_terminal (B : CountableInstance) (N : ℕ) :
    (B.prunedMeanPrefix N).terminal=B.terminal := by
  change (B.meanContractPrefix N).terminal=B.terminal
  exact B.meanContractPrefix_terminal N

@[simp] lemma prunedMeanPrefix_cap (B : CountableInstance) (N : ℕ) :
    (B.prunedMeanPrefix N).cap=B.cap := by
  change (B.meanContractPrefix N).cap=B.cap
  exact B.meanContractPrefix_cap N

lemma prunedMeanPrefix_tail_laws (B : CountableInstance) (N i : ℕ) (hi : N ≤ i) :
    (B.prunedMeanPrefix N).individuals i=B.individuals i := B.meanContractPrefix_tail_laws N i hi

lemma prunedMeanPrefix_contracted_laws (B : CountableInstance) (N i : ℕ) (hi : i<N) :
    ((B.prunedMeanPrefix N).individuals i : Measure ℝ)=Measure.dirac (B.individualMean i) :=
  B.meanContractPrefix_contracted_laws N i hi

lemma meanContractPrefix_expected_tail_eq (B : CountableInstance) (N : ℕ) :
    (B.meanContractPrefix N).expectedIndividualTailExcessMaximum N=B.expectedIndividualTailExcessMaximum N :=
  B.expectedIndividualTailExcessMaximum_eq_of_tail_laws (B.meanContractPrefix N) N
    (B.meanContractPrefix_terminal N) (B.meanContractPrefix_tail_laws N)

lemma prunedMeanPrefix_expected_tail_eq (B : CountableInstance) (N : ℕ) :
    (B.prunedMeanPrefix N).expectedIndividualTailExcessMaximum N=B.expectedIndividualTailExcessMaximum N :=
  B.expectedIndividualTailExcessMaximum_eq_of_tail_laws (B.prunedMeanPrefix N) N
    (B.prunedMeanPrefix_terminal N) (B.prunedMeanPrefix_tail_laws N)

theorem prunedMeanPrefix_preserves_criticality (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (hIndividual : B.AllIndividualDurationScoresZero w c) (hBand : B.AllPositiveBandDurationScoresZero w c)
    (N : ℕ) :
    (B.prunedMeanPrefix N).IsCritical w c ∧
      (B.prunedMeanPrefix N).expectedMaximum=B.expectedMaximum ∧
      (B.prunedMeanPrefix N).optimalScalarValue w c=B.optimalScalarValue w c := by
  let Q := B.meanContractPrefix N
  have hMean := B.meanContractPrefix_preserves_zero_response_criticality hw hc hCritical hIndividual hBand N
  have hTerminal := Q.terminal_eq_zero_of_critical hw hc.le hMean.1
  have hSub : Q.firstBandWindow N ⊆ Ioi (Q.markCutoff N) := by rw [Q.firstBandWindow_eq_tail]
  have hZero := hMean.2.2.2.2 (Q.firstBandWindow N) (Q.measurableSet_firstBandWindow N)
    (Q.markCutoff N) (Q.terminal_lt_markCutoff N) hSub
  have hV := Q.deleteFirstBands_value_eq_of_zero_durationScore hTerminal hw hc N hZero
  have hScalar := Q.scalarBandLikelihoodDerivative_firstBandWindow_eq_zero_of_zero_durationScore hTerminal hw hc N hZero
  have hM := Q.expectedMaximum_scaleBand_zero_eq_of_critical_scalarDerivative_zero hw hc hMean.1
    (Q.measurableSet_firstBandWindow N) (Q.terminal_lt_markCutoff N) hSub hScalar
  have hVTotal : (B.prunedMeanPrefix N).optimalScalarValue w c=B.optimalScalarValue w c := hV.trans hMean.2.2.1
  have hMTotal : (B.prunedMeanPrefix N).expectedMaximum=B.expectedMaximum := hM.trans hMean.2.1
  refine ⟨⟨?_,?_⟩,hMTotal,hVTotal⟩
  · rw [hMTotal]
    exact hCritical.1
  · change (B.prunedMeanPrefix N).optimalScalarValue w c-optimalCompetitiveRatio*
      (w*(B.prunedMeanPrefix N).expectedMaximum+c)=0
    rw [hVTotal,hMTotal]
    exact hCritical.2

end ProphetSecretary.Limiting.CountableInstance
