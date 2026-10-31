import ProphetSecretary.Limiting.CountableValueActionLimit
import ProphetSecretary.Limiting.FirstAcceptanceOutcomeLimit
import ProphetSecretary.Limiting.CountableFixedValuePolicy

/-!
# Fixed-design outcome convergence under independent evaluation laws

Thresholds use fixed design data. Independent evaluation laws supply the
actual offers and clocks. A common acceptance floor, actual positive-level
local finiteness and strict margins give reward/duration convergence on that
common evaluation world.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

theorem valueRule_truncation_outcomes_eval_tendsto_ae (B : CountableInstance) (hZero : B.terminal = 0)
    (Eval : CountableInstance) (hEvalZero : Eval.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ v ∂Eval.completeWorldLaw (Measure.dirac ()),
      Tendsto (fun N => (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedReward Eval.terminal v)
        atTop (𝓝 ((B.valueRule w c).realizedReward Eval.terminal v)) ∧
      Tendsto (fun N => (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedDuration v)
        atTop (𝓝 ((B.valueRule w c).realizedDuration v)) := by
  have hReserve : Eval.terminal ≤ B.terminal := by simp only [hEvalZero,hZero,le_refl]
  have hBand : ∀ᵐ v : CompleteWorld Unit ∂Eval.completeWorldLaw (Measure.dirac ()), ∀ k j,
      ((v.1 k).2 j).1 ∈ Ioo (0 : ℝ) 1 ∧ ((v.1 k).2 j).2 ∈ Ioc (0 : ℝ) Eval.cap :=
    (measurePreserving_fst : MeasurePreserving (fun v : CompleteWorld Unit => v.1)
      (Eval.completeWorldLaw (Measure.dirac ())) Eval.bandConfigurationsLaw).quasiMeasurePreserving.ae Eval.bandConfigurations_supported
  filter_upwards [Eval.completeWorld_locallyFinite (Measure.dirac ()),
    Eval.present_candidate_times_mem_Ioo (Measure.dirac ()),Eval.codeValue_bounded (Measure.dirac ()),
    B.valueRule_candidate_tie_ne_ae hZero Eval hw hc (Measure.dirac ()),B.valueRule_admissible_eval Eval hReserve hw hc,hBand]
      with v hLocal hTimes hValues hTies hFirst hBands
  have hPoint (i : ℕ) (hi : codePresent v i) : ∀ᶠ N in atTop,
      (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).codeAccepted v i ↔
        (B.valueRule w c).codeAccepted v i := by
    have ht : codeTime v i < 1 := (hTimes (candidateEnumeration.symm i) hi).2
    have hTie : B.valueContinuationAtCandidate w c v (candidateEnumeration.symm i) ≠ w*codeValue v i :=
      hTies (candidateEnumeration.symm i) hi
    have hPositive : candidateKind (candidateEnumeration.symm i) = none → 0 < codeValue v i := by
      intro hKind
      cases hj : candidateEnumeration.symm i with
      | inl k => simp only [hj,candidateKind,reduceCtorEq] at hKind
      | inr kj =>
        have hp : kj.2 < (v.1 kj.1).1 := by
          change candidatePresent v (candidateEnumeration.symm i) at hi
          simpa only [hj,candidatePresent] using hi
        change 0 < (candidatePoint v (candidateEnumeration.symm i)).2
        rw [hj]
        simpa only [candidatePoint,configurationPoint,dif_pos hp] using (hBands kj.1 ⟨kj.2,hp⟩).2.1
    exact B.truncatedValueRule_code_eventually hZero hw hc v i ht hPositive hTie
  have hTargetFloor (i : ℕ) (hi : (B.valueRule w c).codeAccepted v i) :
      (c/w)*(1-codeTime v i) ≤ codeValue v i := by
    simpa only [hZero,NNReal.coe_zero,zero_add] using B.valueRule_code_floor hw v i hi
  have hApproxFloor (N i : ℕ)
      (hi : (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).codeAccepted v i) :
      (c/w)*(1-codeTime v i) ≤ codeValue v i := by
    simpa only [hZero,NNReal.coe_zero,zero_add] using B.truncatedValueRule_code_floor N (B.markCutoff N)
      (B.terminal_lt_markCutoff N) hw hc.le v i hi
  have hHigh (d : ℝ) (hd : 0 < d) : {i | codePresent v i ∧ d < codeValue v i}.Finite := by
    apply hLocal d
    simpa only [hEvalZero,NNReal.coe_zero] using hd
  have h := FirstAcceptance.outcomes_tendsto_of_pointwise_actions (B.valueRule w c).codeAccepted
    (fun N => (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).codeAccepted)
    codePresent codeTime codeValue v (div_pos hc hw) Eval.cap.property hHigh
    (fun i hi => hTimes (candidateEnumeration.symm i) hi) hValues
    (fun _ hi => hi.1) (fun _ _ hi => hi.1) hTargetFloor hApproxFloor hFirst hPoint
  simpa only [CountableRule.realizedReward,CountableRule.realizedDuration,hEvalZero,NNReal.coe_zero] using h

end ProphetSecretary.Limiting.CountableInstance
