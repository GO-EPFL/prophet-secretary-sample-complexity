import ProphetSecretary.Limiting.HybridFirstDisagreement
import ProphetSecretary.Limiting.HybridRetainedBand
import ProphetSecretary.Limiting.HybridAnonymousBandProbability
import ProphetSecretary.Limiting.HybridContinuationClockForms
import ProphetSecretary.Limiting.HybridDesignLossComparison

/-!
# Actual candidate forms of the complete hybrid boundary event

The full-vector boundary event splits into retained candidates and anonymous
marks. The actual child continuation ignores past values but retains every
past identity, exactly as in the canonical Markov callback.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

lemma combinedClocks_eq_appendClocks (u : Fin n → ℝ) (p : Fin N → Point) :
    combinedClocks u p = Model.ZeroSimulation.appendClocks u (fun j => (p j).1) := by
  funext k
  induction k using Fin.addCases <;>
    simp only [combinedClocks,Model.ZeroSimulation.appendClocks,Fin.addCases_left,Fin.addCases_right]

lemma FiniteIntensityHybridInstance.retained_acceptanceGap_eq_candidateGap
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (x u : Fin n → ℝ) (p : Fin N → Point) (i : Fin n) :
    w*combinedValues x p (i.castAdd N)-B.finiteContinuationAtArrival w c
      (combinedValues x p) (combinedClocks u p) (i.castAdd N) =
      B.candidateGap w c (some i) (x i) u (u i) := by
  rw [B.finiteContinuationAtArrival_values_invariant w c _ (fun _ => 0)]
  simp only [combinedValues,Fin.addCases_left]
  rw [combinedClocks_eq_appendClocks,B.finiteContinuation_retained_clockForm hw c]
  rfl

lemma FiniteIntensityHybridInstance.anonymous_acceptanceGap_eq_candidateGap
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (x u : Fin n → ℝ) (p : Fin N → Point) (j : Fin N) :
    w*combinedValues x p (j.natAdd n)-B.finiteContinuationAtArrival w c
      (combinedValues x p) (combinedClocks u p) (j.natAdd n) =
      B.candidateGap w c none (p j).2 u (p j).1 := by
  rw [B.finiteContinuationAtArrival_values_invariant w c _ (fun _ => 0)]
  simp only [combinedValues,Fin.addCases_right]
  rw [combinedClocks_eq_appendClocks,B.finiteContinuation_anonymous_clockForm hw c]
  rfl

lemma FiniteIntensityHybridInstance.positiveValueBand_iff
    (B : FiniteIntensityHybridInstance n) {Seed : Type*} {w : ℝ} (hw : 0 < w) (c b e : ℝ)
    (v : HybridWorld n Seed) :
    v ∈ B.positiveValueBand w c b e ↔
      (∃ i : Fin n, v.2 ∈ B.retainedPositiveBand w c b e i) ∨
        (∃ j : Fin v.1.1, v.1.2 j ∈ B.anonymousPositiveBand w c b e v.2.2.1) := by
  constructor
  · rintro ⟨k,hx,hg⟩
    induction k using Fin.addCases with
    | left i =>
      exact Or.inl ⟨i,by
        change b ≤ v.2.1 i ∧ _
        refine ⟨by simpa only [combinedValues,Fin.addCases_left] using hx,?_⟩
        rwa [B.retained_acceptanceGap_eq_candidateGap hw c] at hg⟩
    | right j =>
      exact Or.inr ⟨j,by
        change b ≤ (v.1.2 j).2 ∧ _
        refine ⟨by simpa only [combinedValues,Fin.addCases_right] using hx,?_⟩
        rwa [B.anonymous_acceptanceGap_eq_candidateGap hw c] at hg⟩
  · rintro (⟨i,hx,hg⟩|⟨j,hx,hg⟩)
    · refine ⟨i.castAdd v.1.1,by simpa only [combinedValues,Fin.addCases_left] using hx,?_⟩
      rwa [B.retained_acceptanceGap_eq_candidateGap hw c]
    · refine ⟨j.natAdd n,by simpa only [combinedValues,Fin.addCases_right] using hx,?_⟩
      rwa [B.anonymous_acceptanceGap_eq_candidateGap hw c]

end ProphetSecretary.Limiting
