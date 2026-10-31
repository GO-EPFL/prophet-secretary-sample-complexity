import ProphetSecretary.Limiting.CountableCriticalIndividualTie
import ProphetSecretary.Limiting.CountableMeanScoreInvariance
import ProphetSecretary.Limiting.CountableMeanBandScoreInvariance

/-!
# Finite prefixes of individual mean contractions

The zero-response predicates express the explicit reductio alternative in
`lem:nonzero`. Each actual mean contraction preserves criticality, both
benchmarks, and the zero responses. Iterating finitely many times therefore
requires no convergence of policies or derivatives. Future marginals retain
their original laws; contracted marginals are point masses at the original
means. All identities and independent clocks remain present.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

def AllIndividualDurationScoresZero (B : CountableInstance) (w c : ℝ) : Prop :=
  ∀ (i : ℕ) (φ : ℝ → ℝ), Measurable φ → (∀ x, |φ x|≤1) →
    (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
    (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
      ∂B.completeWorldLaw (Measure.dirac ()))=0

def AllPositiveBandDurationScoresZero (B : CountableInstance) (w c : ℝ) : Prop :=
  ∀ (S : Set ℝ), MeasurableSet S → ∀ (b : ℝ), (B.terminal : ℝ)<b → S ⊆ Ioi b →
    (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()))=0

noncomputable def meanContractPrefix (B : CountableInstance) : ℕ → CountableInstance
  | 0 => B
  | n+1 => (meanContractPrefix B n).contractIndividual n

@[simp] lemma meanContractPrefix_terminal (B : CountableInstance) (n : ℕ) :
    (B.meanContractPrefix n).terminal=B.terminal := by
  induction n with
  | zero => rfl
  | succ n ih => exact (B.meanContractPrefix n).contractIndividual_terminal n |>.trans ih

@[simp] lemma meanContractPrefix_cap (B : CountableInstance) (n : ℕ) :
    (B.meanContractPrefix n).cap=B.cap := by
  induction n with
  | zero => rfl
  | succ n ih => exact (B.meanContractPrefix n).contractIndividual_cap n |>.trans ih

@[simp] lemma meanContractPrefix_intensity (B : CountableInstance) (n : ℕ) :
    (B.meanContractPrefix n).intensity=B.intensity := by
  induction n with
  | zero => rfl
  | succ n ih => exact (B.meanContractPrefix n).contractIndividual_intensity n |>.trans ih

theorem meanContractPrefix_tail_laws (B : CountableInstance) (n : ℕ) :
    ∀ i : ℕ, n ≤ i → (B.meanContractPrefix n).individuals i=B.individuals i := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro i hi
    change ((B.meanContractPrefix n).contractIndividual n).individuals i=B.individuals i
    rw [(B.meanContractPrefix n).contractIndividual_other n i (by omega)]
    exact ih i (by omega)

lemma meanContractPrefix_next_mean (B : CountableInstance) (n : ℕ) :
    (B.meanContractPrefix n).individualMean n=B.individualMean n := by
  unfold individualMean
  rw [B.meanContractPrefix_tail_laws n n le_rfl]

theorem meanContractPrefix_contracted_laws (B : CountableInstance) (n : ℕ) :
    ∀ i : ℕ, i<n → ((B.meanContractPrefix n).individuals i : Measure ℝ)=Measure.dirac (B.individualMean i) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    change (((B.meanContractPrefix n).contractIndividual n).individuals i : Measure ℝ)=_
    by_cases hin : i=n
    · subst i
      rw [(B.meanContractPrefix n).contractIndividual_individual_law,B.meanContractPrefix_next_mean]
    · rw [(B.meanContractPrefix n).contractIndividual_other n i hin]
      exact ih i (by omega)

theorem meanContractPrefix_preserves_zero_response_criticality
    (B : CountableInstance) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (hCritical : B.IsCritical w c) (hIndividual : B.AllIndividualDurationScoresZero w c)
    (hBand : B.AllPositiveBandDurationScoresZero w c) (n : ℕ) :
    (B.meanContractPrefix n).IsCritical w c ∧
      (B.meanContractPrefix n).expectedMaximum=B.expectedMaximum ∧
      (B.meanContractPrefix n).optimalScalarValue w c=B.optimalScalarValue w c ∧
      (B.meanContractPrefix n).AllIndividualDurationScoresZero w c ∧
      (B.meanContractPrefix n).AllPositiveBandDurationScoresZero w c := by
  induction n with
  | zero => exact ⟨hCritical,rfl,rfl,hIndividual,hBand⟩
  | succ n ih =>
    let Q := B.meanContractPrefix n
    have hTerminal := Q.terminal_eq_zero_of_critical hw hc.le ih.1
    have hContraction := Q.critical_mean_contraction hw hc ih.1 n (ih.2.2.2.1 n)
    refine ⟨hContraction.1,hContraction.2.1.trans ih.2.1,hContraction.2.2.trans ih.2.2.1,?_,?_⟩
    · intro i φ hφ hb hMean
      exact Q.canonical_individual_durationScores_zero_after_contraction hTerminal hw hc ih.2.2.2.1 n i φ hφ hb hMean
    · intro S hS b hb hSub
      change (Q.terminal : ℝ)<b at hb
      exact Q.canonical_band_durationScore_zero_after_mean hTerminal hw hc n (ih.2.2.2.1 n)
        hS hb hSub (ih.2.2.2.2 S hS b hb hSub)

end ProphetSecretary.Limiting.CountableInstance
