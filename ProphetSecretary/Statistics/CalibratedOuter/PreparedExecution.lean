import ProphetSecretary.Statistics.CalibratedOuter.CountedTraining
import ProphetSecretary.Statistics.CalibratedOuter.SampleUpperBound
import ProphetSecretary.Model.ComputedSampling

/-!
# Preparing the outer transformation once

The stored cutoff and pilot scale are computed before the online run. A
nonzero scale causes the two inner training blocks to be transformed once.
During execution, the bounded rule receives only the displayed current and
past observations and its own seed.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

private lemma vector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

section Arithmetic
variable {K : Type*} [Field K] [LinearOrder K] {n m : ℕ}

def countedRetention (t z : K × K) : K :=
  if (toLex t : Lex (K × K)) < toLex z then z.1 else 0

def countedDisplay (m : ℕ) (H : K) (t z : K × K) : K × ℕ :=
  let y := countedRetention t z
  let a := countedMeshRound 1 m (min (max 0 (y/H)) 1)
  (a.1,a.2+9)

lemma countedDisplay_work (m : ℕ) (H : K) (t z : K × K) :
    (countedDisplay m H t z).2 ≤ 4*m+18 := by
  have h := countedMeshRound_work (1 : K) m (min (max 0 (countedRetention t z/H)) 1)
  unfold countedDisplay
  dsimp only
  omega

structure CountedOuterPreparation (K : Type*) (n m : ℕ) where
  cutoff : K × K
  pilot : K
  displayed : Fin n → Fin (2*m) → K
  work : ℕ

def countedOuterPrepare (hm : 1≤m) (cut : Fin m → Fin n → K × K)
    (pilot : Fin (outerPilotRounds m) → Fin n → K × K)
    (inner : Fin (2*m) → Fin n → K × K) : CountedOuterPreparation K n m :=
  let t := countedCutoff hm cut
  let p := countedPilot hm t.1 pilot
  if p.1 = 0 then ⟨t.1,p.1,fun _ _ => 0,t.2+p.2+5⟩
  else
    let H := 1000*p.1
    let q : Vector (Vector (K × ℕ) (2*m)) n :=
      Vector.ofFn fun i => Vector.ofFn fun j => countedDisplay m H t.1 (inner j i)
    ⟨t.1,p.1,fun i j => ((q.get i).get j).1,
      t.2+p.2+5 + ∑ i : Fin n, ∑ j : Fin (2*m), (((q.get i).get j).2+3)⟩

theorem countedOuterPrepare_work (hm : 1≤m) (cut : Fin m → Fin n → K × K)
    (pilot : Fin (outerPilotRounds m) → Fin n → K × K) (inner : Fin (2*m) → Fin n → K × K) :
    (countedOuterPrepare hm cut pilot inner).work ≤
      10*(m+1)*(n+1)+20*(outerPilotRounds m+1)^2*(n+1)+5 + n*(2*m)*(4*m+21) := by
  have hT := countedCutoff_work hm cut
  have hP := countedPilot_work hm (countedCutoff hm cut).1 pilot
  unfold countedOuterPrepare
  dsimp only
  split_ifs
  · dsimp only
    omega
  · dsimp only
    have hs : (∑ i : Fin n, ∑ j : Fin (2*m),
        ((countedDisplay m (1000*(countedPilot hm (countedCutoff hm cut).1 pilot).1)
          (countedCutoff hm cut).1 (inner j i)).2+3)) ≤ n*(2*m)*(4*m+21) := by
      calc
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin (2*m), (4*m+21) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have := countedDisplay_work m (1000*(countedPilot hm (countedCutoff hm cut).1 pilot).1)
            (countedCutoff hm cut).1 (inner j i)
          omega
        _ = _ := by simp [Nat.mul_assoc]
    simp only [vector_get_ofFn]
    omega

end Arithmetic

variable {n m : ℕ}

lemma countedRetention_value (t z : ℝ × ℝ) : countedRetention t z = retainAboveTag t z := by
  unfold countedRetention retainAboveTag
  by_cases h : taggedAbove t z <;> simp only [← taggedAbove_iff_lex_lt, h, if_true, if_false]

lemma countedDisplay_value (m : ℕ) (H : ℝ) (t z : ℝ × ℝ) :
    (countedDisplay m H t z).1 = outerMeshDisplay m H (retainAboveTag t z) := by
  unfold countedDisplay outerMeshDisplay outerUnitMesh
  dsimp only
  rw [countedRetention_value]
  exact countedMeshRound_value 1 (by norm_num) m _

noncomputable def preparedOuterInput (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) : CountedOuterPreparation ℝ n m :=
  let c := outerCutoffInput m L p
  let a := outerPilotInput m L p
  let b := outerInnerInput m L p
  countedOuterPrepare hm (taggedTrainingRows c.1 c.2) (taggedTrainingRows a.1 a.2)
    (taggedTrainingRows b.1 b.2)

lemma preparedOuterInput_cutoff (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) :
    (preparedOuterInput m hm L p).cutoff = outerCutoffAt m hm L p := by
  unfold preparedOuterInput countedOuterPrepare
  dsimp only
  split_ifs <;> exact countedCutoff_value _ _

lemma preparedOuterInput_pilot (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) :
    (preparedOuterInput m hm L p).pilot = outerPilotAt m hm L p := by
  unfold preparedOuterInput countedOuterPrepare
  dsimp only
  split_ifs <;> dsimp only <;> rw [countedCutoff_value] <;> exact countedPilot_value _ _ _

lemma preparedOuterInput_displayed (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) (h : outerPilotAt m hm L p ≠ 0) :
    (preparedOuterInput m hm L p).displayed = outerInnerTraining m hm L p := by
  unfold preparedOuterInput countedOuterPrepare
  dsimp only
  have hp : (countedPilot hm
      (countedCutoff hm (taggedTrainingRows (outerCutoffInput m L p).1 (outerCutoffInput m L p).2)).1
      (taggedTrainingRows (outerPilotInput m L p).1 (outerPilotInput m L p).2)).1 =
      outerPilotAt m hm L p := by
    rw [countedCutoff_value]
    exact countedPilot_value _ _ _
  rw [if_neg (by rw [hp]; exact h)]
  funext i j
  simp only [vector_get_ofFn, countedDisplay_value]
  rw [hp, countedCutoff_value]
  rfl

/-- Running the prepared rule requires the current value and the strict
history. The outer seed never passes its online tag vector to the inner rule. -/
noncomputable def decidePreparedOuter (m : ℕ) (L : Learner n (2*m))
    (q : CountedOuterPreparation ℝ n m) (inner : L.Seed) (tags : Fin n → ℝ)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) : Bool :=
  if q.pilot = 0 then decide (0 < countedRetention q.cutoff (x,tags i))
  else
    let f j y := (countedDisplay m (1000*q.pilot) q.cutoff (y,tags j)).1
    L.policy.decide (q.displayed,inner) t i (f i x) (mapHistoryValuesBy f H)

lemma decidePreparedOuter_eq (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    decidePreparedOuter m L (preparedOuterInput m hm L p)
      (outerInnerPolicySeed m L p) (outerOnlineTags m L p) t i x H =
      (outerPolicy m hm L).decide p t i x H := by
  unfold decidePreparedOuter
  rw [preparedOuterInput_pilot]
  by_cases hp : outerPilotAt m hm L p = 0
  · simp only [if_pos hp, countedRetention_value, preparedOuterInput_cutoff, outerPolicy,
      outerPositivePolicy, Policy.pullbackValuesBy, firstPositiveRule, outerRetainedObservation]
    split_ifs with h <;> simp [h]
  · simp only [if_neg hp, preparedOuterInput_displayed m hm L p hp, countedDisplay_value,
      preparedOuterInput_cutoff, outerPolicy, outerBoundedPolicy, Policy.pullbackValuesBy,
      outerDisplayedObservation, outerRetainedObservation]
    rfl

/-- The actual causal full-block request scan, followed by the same prepared
policy. This has the same induced online law as the full-sample model used in
the reduction. -/
noncomputable def computedOuterLearner (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    Learner n (outerSampleBudget m) :=
  Learner.ofComputedSamplePolicy (OuterLearnerSeed m L) (outerLearnerSeedLaw m L)
    (outerPolicy m hm L) (outerPolicy_isMeasurable m hm L)

lemma computedOuterLearner_reward (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) (P : Instance n) :
    (computedOuterLearner m hm L).expectedReward P = (outerLearner m hm L).expectedReward P := by
  have h : (computedOuterLearner m hm L).policy = (outerLearner m hm L).policy := by
    apply congrArg Policy.mk
    funext p t i x H
    exact (Learner.ofComputedSamplePolicy_decide (OuterLearnerSeed m L) (outerLearnerSeedLaw m L)
      (outerPolicy m hm L) (outerPolicy_isMeasurable m hm L) p.1 p.2 t i x H).trans
        (outerLearner_decide m hm L (p.1,p.2) t i x H).symm
  change (∫ ω : World n (OuterLearnerInput m L),
    (computedOuterLearner m hm L).policy.reward ω.2.2 Finset.univ ω.1 ω.2.1
      ∂P.worldLaw ((P.reservoirLaw _).prod (outerLearnerSeedLaw m L))) =
    (∫ ω : World n (OuterLearnerInput m L),
    (outerLearner m hm L).policy.reward ω.2.2 Finset.univ ω.1 ω.2.1
      ∂P.worldLaw ((P.reservoirLaw _).prod (outerLearnerSeedLaw m L)))
  rw [h]
  rfl

lemma computedOuterLearner_requests (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (s : OuterLearnerSeed m L) (y : Reservoir n (outerSampleBudget m)) (i : Fin n) :
    requests (trainingTranscript (computedOuterLearner m hm L).request s y) i =
      3*m+6000*Nat.clog 2 (2*m) := by
  rw [← outerSampleBudget_eq]
  exact Learner.ofComputedSamplePolicy_requests_eq _ _ _ _ y s i

end ProphetSecretary.Statistics.Calibration
