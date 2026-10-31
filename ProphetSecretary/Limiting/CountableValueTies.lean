import ProphetSecretary.Limiting.CountableRetainedTieNull
import ProphetSecretary.Limiting.CountablePoissonTieNull

/-!
# Null acceptance/continuation ties at every actual countable arrival

The design values are fixed while evaluation laws may differ. Retained values
use actual independent clock erasure; anonymous arrivals use actual independent
band laws. Only present candidates are offers, and no uncountable union over
hypothetical unseen masks is taken.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

def candidateKind : Candidate → Option ℕ
  | Sum.inl i => some i
  | Sum.inr _ => none

noncomputable def valueContinuationAtCandidate (B : CountableInstance) (w c : ℝ)
    {Seed : Type*} (v : CompleteWorld Seed) (j : Candidate) : ℝ :=
  let p := candidatePoint v j
  B.continuationValue (candidateMask (unseenMask (individualHistory v.2.1 v.2.2.1 p.1)) (candidateKind j))
    w c (remainingTime p.1)

lemma valueContinuationAtCandidate_eq_clockProfile (B : CountableInstance) (w c : ℝ)
    {Seed : Type*} (v : CompleteWorld Seed) (j : Candidate) :
    B.valueContinuationAtCandidate w c v j =
      B.clockProfile v.2.2.1 (candidateKind j) w c (candidatePoint v j).1 := by
  change B.continuationValue
      (candidateMask (unseenMask (individualHistory v.2.1 v.2.2.1 (candidatePoint v j).1)) (candidateKind j))
      w c (remainingTime (candidatePoint v j).1) =
    B.continuationValue (candidateMask (clockMask v.2.2.1 (candidatePoint v j).1) (candidateKind j))
      w c (remainingTime (candidatePoint v j).1)
  exact congrArg (fun keep : IndividualMask => B.continuationValue (candidateMask keep (candidateKind j))
    w c (remainingTime (candidatePoint v j).1))
      (unseenMask_history_eq_clockMask v.2.1 v.2.2.1 (candidatePoint v j).1)

/-- All actual retained and anonymous arrivals avoid the acceptance equality,
with atoms in their value laws allowed. Design and evaluation are distinct. -/
theorem valueRule_candidate_tie_ne_ae (B : CountableInstance) (hZero : B.terminal = 0) (Eval : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂Eval.completeWorldLaw ν, ∀ j : Candidate, candidatePresent v j →
      B.valueContinuationAtCandidate w c v j ≠ w*(candidatePoint v j).2 := by
  have hR := ae_all_iff.mpr (fun i => B.individual_clockProfile_eval_ne_ae hZero Eval hw hc ν i)
  have hP := B.poisson_clockProfile_eval_ne_ae hZero Eval hw hc ν
  filter_upwards [hR,hP] with v hRet hPois
  intro j hPresent
  rw [B.valueContinuationAtCandidate_eq_clockProfile w c v j]
  cases j with
  | inl i => exact hRet i
  | inr kj => exact hPois kj.1 kj.2 hPresent

end ProphetSecretary.Limiting.CountableInstance
