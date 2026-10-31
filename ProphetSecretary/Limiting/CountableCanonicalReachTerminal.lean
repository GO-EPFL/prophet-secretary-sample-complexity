import ProphetSecretary.Limiting.CountableCanonicalReach
import ProphetSecretary.Limiting.CountableMaskOrderTerminal

/-!
# Actual canonical strict reach with an arbitrary terminal reserve

The deletion-monotone property is proved from actual continuation values,
including the reserve. The fixed measurable callback may be evaluated under
any law for which its first acceptance is almost surely attained.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma clockProfile_antitone_with_terminal (B : CountableInstance)
    (clocks : ℕ → ℝ) (candidate : Option ℕ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Antitone (B.clockProfile clocks candidate w c) := by
  intro s t hst
  have hMasks := maskLe_candidateMask (clockMask_antitone clocks hst) candidate
  have hRem : remainingTime t ≤ remainingTime s :=
    Real.toNNReal_le_toNNReal (sub_le_sub_left hst 1)
  have hMask := B.remainingState_value_mono_mask_with_terminal _ _ hMasks (remainingTime t) hw
    (mul_nonneg hc (remainingTime t).property)
  exact hMask.trans (B.continuationValue_mono _ hw hc hRem)

lemma valueMarkovAcceptance_deletionMonotone_with_terminal (B : CountableInstance)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    DeletionMonotoneCountableAcceptance (B.valueMarkovAcceptance w c) := by
  intro _r t _ht
  constructor
  · intro i A D x _hi hAD hAccept
    change decide (0 < x ∧ B.continuationValue (eraseMask D i) w c (remainingTime t) ≤ w*x)=true at hAccept
    change decide (0 < x ∧ B.continuationValue (eraseMask A i) w c (remainingTime t) ≤ w*x)=true
    have hV : B.continuationValue (eraseMask A i) w c (remainingTime t) ≤
        B.continuationValue (eraseMask D i) w c (remainingTime t) :=
      B.remainingState_value_mono_mask_with_terminal _ _ (maskLe_eraseMask hAD i) _ hw
        (mul_nonneg hc (remainingTime t).property)
    exact decide_eq_true ⟨(of_decide_eq_true hAccept).1,hV.trans (of_decide_eq_true hAccept).2⟩
  · intro A D x hAD hAccept
    change decide (0 < x ∧ B.continuationValue D w c (remainingTime t) ≤ w*x)=true at hAccept
    change decide (0 < x ∧ B.continuationValue A w c (remainingTime t) ≤ w*x)=true
    have hV : B.continuationValue A w c (remainingTime t) ≤ B.continuationValue D w c (remainingTime t) :=
      B.remainingState_value_mono_mask_with_terminal _ _ hAD _ hw (mul_nonneg hc (remainingTime t).property)
    exact decide_eq_true ⟨(of_decide_eq_true hAccept).1,hV.trans (of_decide_eq_true hAccept).2⟩

/-- A fixed canonical callback may be evaluated under any countable law for
which it is an admissible policy. Its monotonicity comes from its base instance. -/
theorem valueRule_strict_reach_under_with_terminal (B D : CountableInstance)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hAdm : (B.valueRule w c).Admissible D (Measure.dirac ())) (i : ℕ) :
    (B.valueRule w c).individualReachProbability D (Measure.dirac ()) i-
      (∫ v, (B.valueRule w c).realizedDuration v ∂D.completeWorldLaw (Measure.dirac ())) ≥
      ((B.valueRule w c).individualSelectionProbability D (Measure.dirac ()) i)^2/2 := by
  have hM : (countableMarkovRule (B.valueMarkovAcceptance w c)).IsMeasurable := by
    rw [← B.valueRule_eq_markovAcceptance]
    exact B.valueRule_isMeasurable hw hc
  have hA : (countableMarkovRule (B.valueMarkovAcceptance w c)).Admissible D (Measure.dirac ()) := by
    rwa [← B.valueRule_eq_markovAcceptance]
  rw [B.valueRule_eq_markovAcceptance]
  exact countableMarkovRule_strict_reach (B.valueMarkovAcceptance w c)
    (B.valueMarkovAcceptance_deletionMonotone_with_terminal hw hc) hM D (Measure.dirac ()) hA i

/-- Canonical policy specialization on the actual full countable law, with
zero-maximum and empty-positive-cloud auxiliary instances included. -/
theorem valuePolicy_strict_individual_reach_with_terminal (B : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    (B.valuePolicy hw hc).individualReachProbability i-(B.valuePolicy hw hc).expectedDuration ≥
      ((B.valuePolicy hw hc).individualSelectionProbability i)^2/2 :=
  B.valueRule_strict_reach_under_with_terminal B hw.le hc.le (B.valueRule_admissible hw hc) i

theorem valuePolicy_expectedDuration_le_individualReach_with_terminal (B : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    (B.valuePolicy hw hc).expectedDuration ≤ (B.valuePolicy hw hc).individualReachProbability i := by
  have h := B.valuePolicy_strict_individual_reach_with_terminal hw hc i
  nlinarith only [h,sq_nonneg ((B.valuePolicy hw hc).individualSelectionProbability i)]

end ProphetSecretary.Limiting.CountableInstance
