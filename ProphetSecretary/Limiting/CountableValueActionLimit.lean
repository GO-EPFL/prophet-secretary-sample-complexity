import ProphetSecretary.Limiting.CountableTruncatedValueRule
import ProphetSecretary.Limiting.CountableValueDecision
import ProphetSecretary.Analysis.StrictComparisonLimit

/-!
# Actual pointwise agreement of finite and countable value decisions

Uniform continuation convergence is used together with proved strict margins
at an actual arrival. Retained identities eventually enter the prefix, and
positive anonymous marks eventually exceed the cutoff. This proves decision
agreement rather than inferring policies from optimized-value convergence.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma truncatedValueRule_candidate_eventually (B : CountableInstance) (hZero : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (v : CompleteWorld Unit) (j : Candidate)
    (ht : (candidatePoint v j).1 < 1)
    (hPositive : candidateKind j = none → 0 < (candidatePoint v j).2)
    (hTie : B.valueContinuationAtCandidate w c v j ≠ w*(candidatePoint v j).2) :
    ∀ᶠ N in atTop,
      ((B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).candidateAction v j = true ↔
        (B.valueRule w c).candidateAction v j = true) := by
  let p := candidatePoint v j
  let H := individualHistory v.2.1 v.2.2.1 p.1
  let M := anonymousHistory v.1 p.1
  let keep := candidateMask (unseenMask H) (candidateKind j)
  let F : ℕ → ℝ := fun N => B.truncatedContinuationValue N (B.markCutoff N) (B.terminal_lt_markCutoff N)
    keep w c (remainingTime p.1)
  have hLimit : Tendsto F atTop (𝓝 (B.valueContinuationAtCandidate w c v j)) :=
    (B.truncatedContinuationValue_uniform_limit hw.le hc.le).tendsto_at (keep,remainingTime p.1)
  have hDecisions := ProphetSecretary.Analysis.eventually_le_iff_of_tendsto_ne hLimit hTie
  have hFull := B.valueRule_candidateAction_iff_preterminal hw hc v j ht
  cases j with
  | inl i =>
    filter_upwards [hDecisions,eventually_gt_atTop i] with N hN hiN
    have hFinite := B.truncatedValueRule_individual_iff N (B.markCutoff N) (B.terminal_lt_markCutoff N)
      hw hc.le v.2.2.2 p.1 i hiN p.2 H M
    change (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).candidateAction v (Sum.inl i) = true ↔
      F N ≤ w*p.2 at hFinite
    exact hFinite.trans (hN.trans hFull.symm)
  | inr kj =>
    have hx : 0 < p.2 := hPositive rfl
    have hLevel : (B.terminal : ℝ) < p.2 := by rw [hZero,NNReal.coe_zero]; exact hx
    have hCut := B.markCutoff_tendsto.eventually (gt_mem_nhds hLevel)
    filter_upwards [hDecisions,hCut] with N hN hCutN
    have hFinite := B.truncatedValueRule_poisson_iff N (B.markCutoff N) (B.terminal_lt_markCutoff N)
      hw hc.le v.2.2.2 p.1 p.2 H M
    change (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).candidateAction v (Sum.inr kj) = true ↔
      B.markCutoff N < p.2 ∧ F N ≤ w*p.2 at hFinite
    have hSimple : (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).candidateAction v (Sum.inr kj) = true ↔
        F N ≤ w*p.2 := by simpa only [hCutN,true_and] using hFinite
    exact hSimple.trans (hN.trans hFull.symm)

lemma truncatedValueRule_code_eventually (B : CountableInstance) (hZero : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (v : CompleteWorld Unit) (i : ℕ)
    (ht : codeTime v i < 1)
    (hPositive : candidateKind (candidateEnumeration.symm i) = none → 0 < codeValue v i)
    (hTie : B.valueContinuationAtCandidate w c v (candidateEnumeration.symm i) ≠ w*codeValue v i) :
    ∀ᶠ N in atTop,
      (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).codeAccepted v i ↔
        (B.valueRule w c).codeAccepted v i := by
  have h := B.truncatedValueRule_candidate_eventually hZero hw hc v (candidateEnumeration.symm i) ht hPositive hTie
  filter_upwards [h] with N hN
  exact and_congr Iff.rfl (and_congr Iff.rfl hN)

end ProphetSecretary.Limiting.CountableInstance
