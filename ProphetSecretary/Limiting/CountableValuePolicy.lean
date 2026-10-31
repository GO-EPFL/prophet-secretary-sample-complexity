import ProphetSecretary.Limiting.CountableValueRule
import ProphetSecretary.Limiting.CountableThresholdExecution
import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# An actual admissible countable continuation-value policy

Waiting gives the lower continuation value wa+cu. At positive weights, every
accepted offer therefore lies above a+(c/w)(1−t). Local finiteness above each
positive reserve level proves attainment of the first acceptance. No optimizer
property is included in the policy constructor.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma continuationValue_waiting_le (B : CountableInstance) (keep : IndividualMask) (w c : ℝ) (u : ℝ≥0) :
    w*(B.terminal : ℝ)+c*(u : ℝ) ≤ B.continuationValue keep w c u :=
  (B.remainingState keep u).waiting_le_value w (c*(u : ℝ))

lemma continuation_acceptance_floor (B : CountableInstance) (keep : IndividualMask)
    {w c t x : ℝ} (hw : 0 < w) (ht : t ≤ 1)
    (hAccept : B.continuationValue keep w c (remainingTime t) ≤ w*x) :
    (B.terminal : ℝ)+(c/w)*(1-t) ≤ x := by
  have hWait := B.continuationValue_waiting_le keep w c (remainingTime t)
  rw [coe_remainingTime ht] at hWait
  have hBound := hWait.trans hAccept
  apply (mul_le_mul_iff_right₀ hw).mp
  have he : w*((B.terminal : ℝ)+(c/w)*(1-t)) = w*(B.terminal : ℝ)+c*(1-t) := by
    calc
      _ = w*(B.terminal : ℝ)+((c/w)*w)*(1-t) := by ring
      _ = _ := by rw [div_mul_cancel₀ c hw.ne']
  rw [he]
  exact hBound

lemma valueRule_candidate_floor (B : CountableInstance) {w c : ℝ} (hw : 0 < w)
    (v : CompleteWorld Unit) (j : Candidate) (ht : (candidatePoint v j).1 ≤ 1)
    (hAction : (B.valueRule w c).candidateAction v j = true) :
    (B.terminal : ℝ)+(c/w)*(1-(candidatePoint v j).1) ≤ (candidatePoint v j).2 := by
  cases j with
  | inl i =>
    exact B.continuation_acceptance_floor
      (eraseMask (unseenMask (individualHistory v.2.1 v.2.2.1 (v.2.2.1 i))) i) hw ht
      (of_decide_eq_true hAction).2
  | inr kj =>
    exact B.continuation_acceptance_floor
      (unseenMask (individualHistory v.2.1 v.2.2.1 (configurationPoint kj.2 (v.1 kj.1)).1)) hw ht
      (of_decide_eq_true hAction).2

lemma valueRule_code_floor (B : CountableInstance) {w c : ℝ} (hw : 0 < w)
    (v : CompleteWorld Unit) (i : ℕ) (hAccepted : (B.valueRule w c).codeAccepted v i) :
    (B.terminal : ℝ)+(c/w)*(1-codeTime v i) ≤ codeValue v i :=
  B.valueRule_candidate_floor hw v (candidateEnumeration.symm i) hAccepted.2.1.2 hAccepted.2.2

lemma valueRule_admissible (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    (B.valueRule w c).Admissible B (Measure.dirac ()) :=
  CountableRule.admissible_of_linear_floor B (Measure.dirac ()) (B.valueRule w c) (div_pos hc hw)
    (fun v i hi => B.valueRule_code_floor hw v i hi)

noncomputable def valuePolicy (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    RandomizedCountablePolicy B where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := B.valueRule w c
  measurable_rule := B.valueRule_isMeasurable hw.le hc.le
  admissible := B.valueRule_admissible hw hc

end ProphetSecretary.Limiting.CountableInstance
