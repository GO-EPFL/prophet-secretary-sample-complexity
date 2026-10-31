import ProphetSecretary.Limiting.CountableHorizonReach

/-!
# Canonical reach on a physical remaining horizon

The normalized state's canonical callback is evaluated at physical elapsed
time divided by its positive horizon. The current value and unseen identity
mask are preserved. For physical duration weight c and horizon u, the
normalized state's duration weight is cu; rewards are unchanged and physical
duration is u times normalized duration.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def valueRuleAt (B : CountableInstance) (w c h : ℝ) : CountableRule Unit :=
  countableMarkovRule (fun r A t i x => B.valueMarkovAcceptance w c r A (t/h) i x)

lemma valueRuleAt_onUnitHorizon (B : CountableInstance) (w c : ℝ) {h : ℝ} (hh : 0 < h) :
    (B.valueRuleAt w c h).onUnitHorizon h=B.valueRule w c := by
  unfold valueRuleAt
  rw [countableMarkovRule_onUnitHorizon,B.valueRule_eq_markovAcceptance]
  congr 1
  funext r A t i x
  rw [mul_div_cancel_left₀ t hh.ne']

lemma valueRuleAt_eq_inverse_transport (B : CountableInstance) (w c h : ℝ) :
    B.valueRuleAt w c h=(B.valueRule w c).onUnitHorizon h⁻¹ := by
  rw [B.valueRule_eq_markovAcceptance,countableMarkovRule_onUnitHorizon]
  unfold valueRuleAt
  congr 1
  funext r A t i x
  rw [div_eq_mul_inv,mul_comm t h⁻¹]

lemma valueRuleAt_isMeasurable (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (h : ℝ) :
    (B.valueRuleAt w c h).IsMeasurable := by
  rw [B.valueRuleAt_eq_inverse_transport]
  exact (B.valueRule w c).onUnitHorizon_isMeasurable (B.valueRule_isMeasurable hw hc) h⁻¹

lemma valueRuleAt_admissible (B : CountableInstance) {w c h : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hh : 0 < h) :
    (B.valueRuleAt w c h).AdmissibleAt B (Measure.dirac ()) h := by
  apply ((B.valueRuleAt w c h).admissibleAt_iff_onUnit B (Measure.dirac ()) hh).mpr
  rw [B.valueRuleAt_onUnitHorizon w c hh]
  exact B.valueRule_admissible hw hc

/-- The canonical comparison uses physical additional duration divided by the
horizon. The duration coefficient c here belongs to the normalized state. -/
theorem valueRuleAt_strict_individual_reach (B : CountableInstance) (hZero : B.terminal=0)
    {w c h : ℝ} (hw : 0 < w) (hc : 0 < c) (hh : 0 < h) (i : ℕ) :
    (B.valueRuleAt w c h).individualReachProbabilityAt h B (Measure.dirac ()) i-
      (B.valueRuleAt w c h).expectedDurationAt h B (Measure.dirac ())/h ≥
      ((B.valueRuleAt w c h).individualSelectionProbabilityAt h B (Measure.dirac ()) i)^2/2 := by
  rw [(B.valueRuleAt w c h).individualReachProbabilityAt_eq B (Measure.dirac ()) hh,
    (B.valueRuleAt w c h).individualSelectionProbabilityAt_eq B (Measure.dirac ()) hh,
    (B.valueRuleAt w c h).normalized_expectedDurationAt_eq B (Measure.dirac ()) hh,
    B.valueRuleAt_onUnitHorizon w c hh]
  exact B.valueRule_strict_reach_under B hZero hw hc (B.valueRule_admissible hw hc) i

/-- A normalized remaining instance has intensity multiplied by u. After
physical time scaling by u, its duration coefficient cu corresponds to the
original physical coefficient c. No positivity of expected maximum is needed. -/
theorem remainingState_strict_individual_reachAt (B : CountableInstance) (hZero : B.terminal=0)
    (keep : IndividualMask) {u : ℝ≥0} (hu : 0 < u) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    let D := B.remainingState keep u
    let π := D.valueRuleAt w (c*(u : ℝ)) (u : ℝ)
    π.individualReachProbabilityAt (u : ℝ) D (Measure.dirac ()) i-
      π.expectedDurationAt (u : ℝ) D (Measure.dirac ())/(u : ℝ) ≥
      (π.individualSelectionProbabilityAt (u : ℝ) D (Measure.dirac ()) i)^2/2 := by
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  exact (B.remainingState keep u).valueRuleAt_strict_individual_reach hZero hw (mul_pos hc huR) huR i

end ProphetSecretary.Limiting.CountableInstance
