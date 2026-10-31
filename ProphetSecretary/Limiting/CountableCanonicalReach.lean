import ProphetSecretary.Limiting.CountableStrictReach
import ProphetSecretary.Limiting.CountableClockProfile
import ProphetSecretary.Limiting.CountableValuePolicy

/-!
# Canonical specialization of full countable strict reach

Actual continuation values increase when unseen identities are added, by the
proved zero-variable and mask value comparisons. The canonical callbacks are
therefore deletion-monotone Markov decisions. The positive-value gate is kept
in the exact callback; at positive weights it is redundant before terminal
time, as proved in `CountableValueDecision`.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def valueMarkovAcceptance (B : CountableInstance) (w c : ℝ) :
    Unit → IndividualMask → ℝ → Option ℕ → ℝ → Bool :=
  fun _ keep t candidate x => decide (0 < x ∧
    B.continuationValue (candidateMask keep candidate) w c (remainingTime t) ≤ w*x)

lemma valueRule_eq_markovAcceptance (B : CountableInstance) (w c : ℝ) :
    B.valueRule w c=countableMarkovRule (B.valueMarkovAcceptance w c) := rfl

lemma valueMarkovAcceptance_deletionMonotone (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    DeletionMonotoneCountableAcceptance (B.valueMarkovAcceptance w c) := by
  intro _r t _ht
  constructor
  · intro i A D x _hi hAD hAccept
    change decide (0 < x ∧ B.continuationValue (eraseMask D i) w c (remainingTime t) ≤ w*x)=true at hAccept
    change decide (0 < x ∧ B.continuationValue (eraseMask A i) w c (remainingTime t) ≤ w*x)=true
    have hV : B.continuationValue (eraseMask A i) w c (remainingTime t) ≤
        B.continuationValue (eraseMask D i) w c (remainingTime t) :=
      B.remainingState_value_mono_mask hZero _ _ (maskLe_eraseMask hAD i) _ hw
        (mul_nonneg hc (remainingTime t).property)
    exact decide_eq_true ⟨(of_decide_eq_true hAccept).1,hV.trans (of_decide_eq_true hAccept).2⟩
  · intro A D x hAD hAccept
    change decide (0 < x ∧ B.continuationValue D w c (remainingTime t) ≤ w*x)=true at hAccept
    change decide (0 < x ∧ B.continuationValue A w c (remainingTime t) ≤ w*x)=true
    have hV : B.continuationValue A w c (remainingTime t) ≤ B.continuationValue D w c (remainingTime t) :=
      B.remainingState_value_mono_mask hZero _ _ hAD _ hw (mul_nonneg hc (remainingTime t).property)
    exact decide_eq_true ⟨(of_decide_eq_true hAccept).1,hV.trans (of_decide_eq_true hAccept).2⟩

/-- A fixed canonical callback may be evaluated under any countable law for
which it is an admissible policy. Its monotonicity comes from its base instance. -/
theorem valueRule_strict_reach_under (B D : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hAdm : (B.valueRule w c).Admissible D (Measure.dirac ())) (i : ℕ) :
    (B.valueRule w c).individualReachProbability D (Measure.dirac ()) i-
      (∫ v, (B.valueRule w c).realizedDuration v ∂D.completeWorldLaw (Measure.dirac ())) ≥
      ((B.valueRule w c).individualSelectionProbability D (Measure.dirac ()) i)^2/2 := by
  have hM : (countableMarkovRule (B.valueMarkovAcceptance w c)).IsMeasurable := by
    rw [← B.valueRule_eq_markovAcceptance]
    exact B.valueRule_isMeasurable hw.le hc.le
  have hA : (countableMarkovRule (B.valueMarkovAcceptance w c)).Admissible D (Measure.dirac ()) := by
    rwa [← B.valueRule_eq_markovAcceptance]
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_strict_reach (B.valueMarkovAcceptance w c)
    (B.valueMarkovAcceptance_deletionMonotone hZero hw.le hc.le) hM D (Measure.dirac ()) hA i

/-- Canonical policy specialization on the actual full countable law, with
zero-maximum and empty-positive-cloud auxiliary instances included. -/
theorem valuePolicy_strict_individual_reach (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    (B.valuePolicy hw hc).individualReachProbability i-(B.valuePolicy hw hc).expectedDuration ≥
      ((B.valuePolicy hw hc).individualSelectionProbability i)^2/2 :=
  B.valueRule_strict_reach_under B hZero hw hc (B.valueRule_admissible hw hc) i

theorem valuePolicy_expectedDuration_le_individualReach (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    (B.valuePolicy hw hc).expectedDuration ≤ (B.valuePolicy hw hc).individualReachProbability i := by
  have h := B.valuePolicy_strict_individual_reach hZero hw hc i
  nlinarith only [h,sq_nonneg ((B.valuePolicy hw hc).individualSelectionProbability i)]

end ProphetSecretary.Limiting.CountableInstance
