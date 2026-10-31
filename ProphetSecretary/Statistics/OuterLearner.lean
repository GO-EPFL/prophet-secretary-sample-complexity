import ProphetSecretary.Statistics.OuterCutoff
import ProphetSecretary.Statistics.OuterCapPilot
import ProphetSecretary.Statistics.OuterTrainingBlocks
import ProphetSecretary.Statistics.OuterTransformedTraining

/-!
# The law-independent outer learner

Independent tags accompany each cutoff, pilot, inner, and online observation.
The bounded learner receives only transformed samples, its original seed, and
transformed current and past observations. In particular the vector of online
tags is not supplied to that learner. Present zero observations remain present.
Paper correspondence: `upouter:construction` and `upouter:budget`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

abbrev OuterLearnerSeed (m : ℕ) (L : Learner n (4*m)) :=
  (Fin m → Fin n → ℝ) × ((Fin (outerPilotRounds m) → Fin n → ℝ) ×
    ((Fin (4*m) → Fin n → ℝ) × ((Fin n → ℝ) × L.Seed)))

noncomputable def outerLearnerSeedLaw (m : ℕ) (L : Learner n (4*m)) : Measure (OuterLearnerSeed m L) :=
  (outerTagRowsLaw n m).prod ((outerTagRowsLaw n (outerPilotRounds m)).prod
    ((outerTagRowsLaw n (4*m)).prod ((Instance.clocksLaw n).prod L.seedLaw)))

instance outerLearnerSeedLaw_probability (m : ℕ) (L : Learner n (4*m)) :
    IsProbabilityMeasure (outerLearnerSeedLaw m L) := by
  unfold outerLearnerSeedLaw
  infer_instance

abbrev OuterLearnerInput (m : ℕ) (L : Learner n (4*m)) := Reservoir n (outerSampleBudget m) × OuterLearnerSeed m L

noncomputable def outerCutoffInput (m : ℕ) (L : Learner n (4*m)) (p : OuterLearnerInput m L) :
    Reservoir n m × (Fin m → Fin n → ℝ) := ((outerReservoirBlocks n m p.1).1,p.2.1)

noncomputable def outerPilotInput (m : ℕ) (L : Learner n (4*m)) (p : OuterLearnerInput m L) :
    Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ) :=
  ((outerReservoirBlocks n m p.1).2.1,p.2.2.1)

noncomputable def outerInnerInput (m : ℕ) (L : Learner n (4*m)) (p : OuterLearnerInput m L) :
    Reservoir n (4*m) × (Fin (4*m) → Fin n → ℝ) :=
  ((outerReservoirBlocks n m p.1).2.2,p.2.2.2.1)

lemma measurable_outerCutoffInput (m : ℕ) (L : Learner n (4*m)) : Measurable (outerCutoffInput m L) :=
  (measurable_fst.comp ((outerReservoirBlocks n m).measurable.comp measurable_fst)).prodMk
    (measurable_fst.comp measurable_snd)

lemma measurable_outerPilotInput (m : ℕ) (L : Learner n (4*m)) : Measurable (outerPilotInput m L) :=
  (measurable_fst.comp (measurable_snd.comp ((outerReservoirBlocks n m).measurable.comp measurable_fst))).prodMk
    (measurable_fst.comp (measurable_snd.comp measurable_snd))

lemma measurable_outerInnerInput (m : ℕ) (L : Learner n (4*m)) : Measurable (outerInnerInput m L) :=
  (measurable_snd.comp (measurable_snd.comp ((outerReservoirBlocks n m).measurable.comp measurable_fst))).prodMk
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

noncomputable def outerCutoffAt (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (p : OuterLearnerInput m L) : ℝ × ℝ :=
  outerCutoff m hm (outerCutoffInput m L p)

lemma measurable_outerCutoffAt (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Measurable (outerCutoffAt m hm L) :=
  (measurable_outerCutoff m hm).comp (measurable_outerCutoffInput m L)

noncomputable def outerPilotAt (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (p : OuterLearnerInput m L) : ℝ :=
  outerPilotValue m hm (outerCutoffAt m hm L p) (outerPilotInput m L p)

lemma measurable_outerPilotAt (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Measurable (outerPilotAt m hm L) := by
  have hInput : Measurable (fun p : OuterLearnerInput m L => (outerCutoffAt m hm L p,outerPilotInput m L p)) :=
    (measurable_outerCutoffAt m hm L).prodMk (measurable_outerPilotInput m L)
  have h := (measurable_outerPilotValue (n:=n) m hm).comp hInput
  have hEq : outerPilotAt m hm L=(fun p : OuterLearnerInput m L => outerPilotValue m hm (outerCutoffAt m hm L p) (outerPilotInput m L p)) := rfl
  rw [hEq]
  simpa only [Function.comp_def] using h

lemma outerPilotAt_nonnegative (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (p : OuterLearnerInput m L) :
    0≤outerPilotAt m hm L p := outerPilotValue_nonnegative m hm _ _

noncomputable def outerInnerTraining (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (p : OuterLearnerInput m L) : Reservoir n (4*m) :=
  outerTransformedReservoir m (outerCutoffAt m hm L p) (1000*outerPilotAt m hm L p) (outerInnerInput m L p)

lemma measurable_outerInnerTraining (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Measurable (outerInnerTraining m hm L) :=
  (measurable_outerTransformedReservoir m).comp
    (((measurable_outerCutoffAt m hm L).prodMk (measurable_const.mul (measurable_outerPilotAt m hm L))).prodMk
      (measurable_outerInnerInput m L))

def outerInnerPolicySeed (m : ℕ) (L : Learner n (4*m)) (p : OuterLearnerInput m L) : L.Seed := p.2.2.2.2.2

def outerOnlineTags (m : ℕ) (L : Learner n (4*m)) (p : OuterLearnerInput m L) : Fin n → ℝ := p.2.2.2.2.1

lemma measurable_outerInnerPolicySeed (m : ℕ) (L : Learner n (4*m)) : Measurable (outerInnerPolicySeed m L) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

lemma measurable_outerOnlineTags (m : ℕ) (L : Learner n (4*m)) : Measurable (outerOnlineTags m L) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

noncomputable def outerRetainedObservation (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (i : Fin n) (x : ℝ) : ℝ :=
  retainAboveTag (outerCutoffAt m hm L p) (x,outerOnlineTags m L p i)

lemma measurable_outerRetainedObservation (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (i : Fin n) :
    Measurable (fun p : OuterLearnerInput m L × ℝ => outerRetainedObservation m hm L p.1 i p.2) :=
  measurable_retainAboveTag.comp ((measurable_outerCutoffAt m hm L).comp measurable_fst |>.prodMk
    (measurable_snd.prodMk (((measurable_pi_apply i).comp (measurable_outerOnlineTags m L)).comp measurable_fst)))

noncomputable def outerDisplayedObservation (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (i : Fin n) (x : ℝ) : ℝ :=
  outerMeshDisplay m (1000*outerPilotAt m hm L p) (outerRetainedObservation m hm L p i x)

lemma measurable_outerDisplayedObservation (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (i : Fin n) :
    Measurable (fun p : OuterLearnerInput m L × ℝ => outerDisplayedObservation m hm L p.1 i p.2) :=
  (measurable_outerMeshDisplay m).comp
    ((measurable_const.mul ((measurable_outerPilotAt m hm L).comp measurable_fst)).prodMk
      (measurable_outerRetainedObservation m hm L i))

noncomputable def outerPositivePolicy (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Policy (OuterLearnerInput m L) n :=
  (firstPositiveRule Unit n).pullbackValuesBy (fun _ => ()) (outerRetainedObservation m hm L)

noncomputable def outerBoundedPolicy (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Policy (OuterLearnerInput m L) n :=
  L.policy.pullbackValuesBy (fun p => (outerInnerTraining m hm L p,outerInnerPolicySeed m L p)) (outerDisplayedObservation m hm L)

noncomputable def outerPolicy (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Policy (OuterLearnerInput m L) n where
  decide p t i x h := if outerPilotAt m hm L p=0 then (outerPositivePolicy m hm L).decide p t i x h
    else (outerBoundedPolicy m hm L).decide p t i x h

lemma outerPolicy_isMeasurable (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : (outerPolicy m hm L).IsMeasurable := by
  have hPos := (firstPositiveRule Unit n).pullbackValuesBy_isMeasurable
    (firstPositiveRule_isMeasurable (Seed:=Unit) (n:=n)) (fun _ : OuterLearnerInput m L => ()) measurable_const
      (outerRetainedObservation m hm L) (measurable_outerRetainedObservation m hm L)
  have hBound := L.policy.pullbackValuesBy_isMeasurable L.policy_isMeasurable
    (fun p => (outerInnerTraining m hm L p,outerInnerPolicySeed m L p))
    ((measurable_outerInnerTraining m hm L).prodMk (measurable_outerInnerPolicySeed m L))
    (outerDisplayedObservation m hm L) (measurable_outerDisplayedObservation m hm L)
  exact hPos.ite (measurableSet_eq_fun ((measurable_outerPilotAt m hm L).comp measurable_fst) measurable_const) hBound

noncomputable def outerLearner (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) : Learner n (outerSampleBudget m) :=
  Learner.ofSamplePolicy (OuterLearnerSeed m L) (outerLearnerSeedLaw m L) (outerPolicy m hm L) (outerPolicy_isMeasurable m hm L)

lemma outerLearner_hardBudget (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (r : OuterLearnerSeed m L) (y : Reservoir n (outerSampleBudget m)) (i : Fin n) :
    requests (trainingTranscript (outerLearner m hm L).request r y) i≤5*m+500*⌈12*Real.log (2*(m:ℝ))⌉₊ := by
  rw [←outerSampleBudget_eq]
  exact (outerLearner m hm L).hard_budget r y i

end ProphetSecretary.Statistics
