import ProphetSecretary.Statistics.WeightedCriticalMoments

/-!
# First true critical prefixes on a finite observation grid

The first grid entrance is selected solely from true laws and elapsed clocks.
Its events are observable at their respective times and pairwise disjoint.
The remaining-size multiplier is bounded and therefore may multiply the actual
localized conditional moments without revealing training samples.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

def Instance.firstCriticalGridEvent (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ) (j : ℕ)
    (u : Fin n → ℝ) : Prop :=
  P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ j) u) (1-τ j) 1 hi ≤ a ∧
    ∀ l < j, ¬P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ l) u) (1-τ l) 1 hi ≤ a

omit [NeZero k] in
lemma Instance.measurableSet_firstCriticalGridEvent (P : Instance n) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (hi a : ℝ) (j : ℕ) :
    MeasurableSet[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n (τ j)]
      {q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) | P.firstCriticalGridEvent τ hi a j q.2} := by
  apply (measurableSet_le (P.measurable_observedContinuationValue (τ j) hi) measurable_const).inter
  change MeasurableSet[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n (τ j)]
    {q | ∀ l, l < j → ¬P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ l) q.2) (1-τ l) 1 hi ≤ a}
  rw [setOf_forall]
  apply MeasurableSet.iInter
  intro l
  by_cases hl : l < j
  · have he : MeasurableSet[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n (τ l)]
        {q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) |
          P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ l) q.2) (1-τ l) 1 hi ≤ a} :=
      measurableSet_le (P.measurable_observedContinuationValue (τ l) hi) measurable_const
    have hsig := ProphetSecretary.Probability.observedClockSigma_mono (n := n)
      (D := (Fin n × Fin k) → ℝ) (hτ hl.le)
    have hE := hsig _ he.compl
    simpa only [hl, true_implies, Set.compl_setOf] using hE
  · simp only [hl, false_implies, setOf_true, MeasurableSet.univ]

omit [NeZero k] in
lemma Instance.firstCriticalGridEvent_unique (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ)
    {j l : ℕ} (u : Fin n → ℝ) (hj : P.firstCriticalGridEvent τ hi a j u)
    (hl : P.firstCriticalGridEvent τ hi a l u) : j = l := by
  rcases lt_trichotomy j l with h | h | h
  · exact False.elim (hl.2 j h hj.1)
  · exact h
  · exact False.elim (hj.2 l h hl.1)

noncomputable def Instance.gridEntranceSizeMultiplier (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ) (j : ℕ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  if P.firstCriticalGridEvent τ hi a j q.2 then
    (P.restrictTo (ProphetSecretary.Probability.pendingClockSet (τ j) q.2)).totalFirstMoment + (1-τ j) else 0

omit [NeZero k] in
lemma Instance.stronglyMeasurable_gridEntranceSizeMultiplier (P : Instance n) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (hi a : ℝ) (j : ℕ) :
    StronglyMeasurable[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n (τ j)]
      (P.gridEntranceSizeMultiplier (k := k) τ hi a j) :=
  (Measurable.ite (P.measurableSet_firstCriticalGridEvent τ hτ hi a j)
    (P.measurable_observedRemainingSize (τ j)) measurable_const).stronglyMeasurable

omit [NeZero k] in
lemma Instance.gridEntranceSizeMultiplier_mem (P : Instance n) (τ : ℕ → ℝ) (hi a : ℝ) (j : ℕ)
    (ht0 : 0 ≤ τ j) (ht1 : τ j ≤ 1) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    P.gridEntranceSizeMultiplier τ hi a j q ∈ Icc (0 : ℝ) (P.totalFirstMoment+1) := by
  unfold gridEntranceSizeMultiplier
  split_ifs
  · exact P.observedRemainingSize_mem ht0 ht1 q.2
  · exact ⟨le_rfl, by linarith [P.totalFirstMoment_nonnegative]⟩

/-- A single grid entrance has the source's weighted localized moment bound. -/
theorem Instance.gridEntrance_weighted_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (j : ℕ) (ht0 : 0 ≤ τ j) (ht1 : τ j < 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    (∫ q, P.gridEntranceSizeMultiplier τ hi a j q * P.stateFutureError k lo hi (τ j) q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * ∫ q, P.gridEntranceSizeMultiplier τ hi a j q
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
  apply P.weighted_critical_stateFutureError_moment hbound hlo hlohi hhi ht0 ht1 hp
    (P.gridEntranceSizeMultiplier τ hi a j) (P.stronglyMeasurable_gridEntranceSizeMultiplier τ hτ hi a j)
    (by linarith [P.totalFirstMoment_nonnegative] : 0 ≤ P.totalFirstMoment+1)
    (Eventually.of_forall fun q => P.gridEntranceSizeMultiplier_mem τ hi a j ht0 ht1.le q)
  intro q hne
  by_cases he : P.firstCriticalGridEvent τ hi a j q.2
  · exact he.1
  · exact False.elim (hne (if_neg he))

end ProphetSecretary.Model
