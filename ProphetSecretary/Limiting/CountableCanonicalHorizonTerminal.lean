import ProphetSecretary.Limiting.CountableCanonicalHorizon
import ProphetSecretary.Limiting.CountableCanonicalReachTerminal

/-!
# Canonical reach with reserve on a physical remaining horizon

Time transport preserves reach and selection, and scales actual duration by
the positive horizon. The canonical callback keeps its terminal reserve.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

theorem valueRuleAt_strict_reach_under_with_terminal (B D : CountableInstance)
    {w c h : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hh : 0 < h)
    (hAdm : (B.valueRuleAt w c h).AdmissibleAt D (Measure.dirac ()) h) (i : ℕ) :
    (B.valueRuleAt w c h).individualReachProbabilityAt h D (Measure.dirac ()) i -
      (B.valueRuleAt w c h).expectedDurationAt h D (Measure.dirac ()) / h ≥
      ((B.valueRuleAt w c h).individualSelectionProbabilityAt h D (Measure.dirac ()) i)^2 / 2 := by
  have hA : (B.valueRule w c).Admissible D (Measure.dirac ()) := by
    have h := ((B.valueRuleAt w c h).admissibleAt_iff_onUnit D (Measure.dirac ()) hh).mp hAdm
    rwa [B.valueRuleAt_onUnitHorizon w c hh] at h
  rw [(B.valueRuleAt w c h).individualReachProbabilityAt_eq D (Measure.dirac ()) hh,
    (B.valueRuleAt w c h).individualSelectionProbabilityAt_eq D (Measure.dirac ()) hh,
    (B.valueRuleAt w c h).normalized_expectedDurationAt_eq D (Measure.dirac ()) hh,
    B.valueRuleAt_onUnitHorizon w c hh]
  exact B.valueRule_strict_reach_under_with_terminal D hw hc hA i

/-- The canonical comparison uses physical additional duration divided by the
horizon. The duration coefficient c here belongs to the normalized state. -/
theorem valueRuleAt_strict_individual_reach_with_terminal (B : CountableInstance)
    {w c h : ℝ} (hw : 0 < w) (hc : 0 < c) (hh : 0 < h) (i : ℕ) :
    (B.valueRuleAt w c h).individualReachProbabilityAt h B (Measure.dirac ()) i-
      (B.valueRuleAt w c h).expectedDurationAt h B (Measure.dirac ())/h ≥
      ((B.valueRuleAt w c h).individualSelectionProbabilityAt h B (Measure.dirac ()) i)^2/2 := by
  rw [(B.valueRuleAt w c h).individualReachProbabilityAt_eq B (Measure.dirac ()) hh,
    (B.valueRuleAt w c h).individualSelectionProbabilityAt_eq B (Measure.dirac ()) hh,
    (B.valueRuleAt w c h).normalized_expectedDurationAt_eq B (Measure.dirac ()) hh,
    B.valueRuleAt_onUnitHorizon w c hh]
  exact B.valueRule_strict_reach_under_with_terminal B hw.le hc.le (B.valueRule_admissible hw hc) i

/-- A normalized remaining instance has intensity multiplied by u. After
physical time scaling by u, its duration coefficient cu corresponds to the
original physical coefficient c. No positivity of expected maximum is needed. -/
theorem remainingState_strict_individual_reachAt_with_terminal (B : CountableInstance)
    (keep : IndividualMask) {u : ℝ≥0} (hu : 0 < u) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    let D := B.remainingState keep u
    let π := D.valueRuleAt w (c*(u : ℝ)) (u : ℝ)
    π.individualReachProbabilityAt (u : ℝ) D (Measure.dirac ()) i-
      π.expectedDurationAt (u : ℝ) D (Measure.dirac ())/(u : ℝ) ≥
      (π.individualSelectionProbabilityAt (u : ℝ) D (Measure.dirac ()) i)^2/2 := by
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  exact (B.remainingState keep u).valueRuleAt_strict_individual_reach_with_terminal hw (mul_pos hc huR) huR i

end ProphetSecretary.Limiting.CountableInstance
