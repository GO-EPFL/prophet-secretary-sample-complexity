import ProphetSecretary.Model.OuterRetainedMaximum
import ProphetSecretary.Statistics.OuterTaggedTraining
import ProphetSecretary.Statistics.CalibratedOuter.PilotSchedule

/-!
# The cap pilot as an actual sampling program

The value B uses only the fixed cutoff, q raw full rounds, and independent tags.
Its definition contains no population law. The actual product-law map proves
that its numerical retained maxima are iid with the conditional maximum law.
The transcript and hard q-per-distribution budget hold on every raw outcome.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n q : ℕ}

noncomputable def retainedPilotSamples (t : ℝ × ℝ) (a : Fin q → Fin n → ℝ × ℝ) : Fin q → ℝ :=
  fun r => retainedMaximumAtTag t (a r)

lemma measurable_retainedPilotSamples : Measurable (fun p : (ℝ × ℝ) × (Fin q → Fin n → ℝ × ℝ) => retainedPilotSamples p.1 p.2) := by
  apply measurable_pi_lambda
  intro r
  have hInput : Measurable (fun p : (ℝ × ℝ) × (Fin q → Fin n → ℝ × ℝ) => (p.1,p.2 r)) :=
    measurable_fst.prodMk ((measurable_pi_apply r).comp measurable_snd)
  simpa only [Function.comp_def,retainedPilotSamples] using (measurable_retainedMaximumAtTag (n:=n)).comp hInput

lemma retainedPilotSamples_measurePreserving (P : Instance n) (q : ℕ) (t : ℝ × ℝ) :
    MeasurePreserving (retainedPilotSamples (n:=n) (q:=q) t) (Measure.pi (fun _ : Fin q => P.taggedValuesLaw))
      (Measure.pi (fun _ : Fin q => P.retainedMaximumLaw t)) := by
  have hSingle := P.retainedMaximum_measurePreserving t
  refine ⟨measurable_pi_lambda _ (fun r => hSingle.measurable.comp (measurable_pi_apply r)),?_⟩
  change Measure.map (fun a : Fin q → Fin n → ℝ × ℝ => fun r => retainedMaximumAtTag t (a r))
    (Measure.pi (fun _ : Fin q => P.taggedValuesLaw))=_
  rw [Measure.pi_map_pi (fun _ => hSingle.measurable.aemeasurable)]
  simp only [hSingle.map_eq]

noncomputable def outerPilotValue (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ)
    (p : Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) : ℝ :=
  numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm)
    (retainedPilotSamples t (taggedTrainingRows p.1 p.2))

lemma measurable_outerPilotValue (m : ℕ) (hm : 1≤m) :
    Measurable (fun p : (ℝ × ℝ) × (Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) => outerPilotValue m hm p.1 p.2) := by
  have hInput : Measurable (fun p : (ℝ × ℝ) × (Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) =>
      (p.1,taggedTrainingRows p.2.1 p.2.2)) :=
    measurable_fst.prodMk ((measurable_taggedTrainingRows (n:=n) (q:=outerPilotRounds m)).comp measurable_snd)
  have hSamples : Measurable (fun p : (ℝ × ℝ) × (Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) =>
      retainedPilotSamples p.1 (taggedTrainingRows p.2.1 p.2.2)) := by
    simpa only [Function.comp_def] using (measurable_retainedPilotSamples (n:=n) (q:=outerPilotRounds m)).comp hInput
  convert (measurable_numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm)).comp hSamples using 1
  funext p
  rfl

lemma outerPilotValue_nonnegative (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ)
    (p : Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) : 0≤outerPilotValue m hm t p :=
  sampleOrderStatistic_nonnegative (outerPilotRank m) (outerPilotRank_pos hm) (outerPilotRank_bound (outerPilotRank m))
    (retainedPilotSamples t (taggedTrainingRows p.1 p.2)) (fun _ => Instance.maximum_nonnegative _)

noncomputable def outerPilotFromTranscript (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ)
    (tags : Fin (outerPilotRounds m) → Fin n → ℝ) (T : Transcript n) : ℝ :=
  outerPilotValue m hm t (decodedReservoir T,tags)

lemma measurable_outerPilotFromTranscript (m : ℕ) (hm : 1≤m) :
    Measurable (fun p : (ℝ × ℝ) × ((Fin (outerPilotRounds m) → Fin n → ℝ) × Transcript n) =>
      outerPilotFromTranscript m hm p.1 p.2.1 p.2.2) := by
  have hInput : Measurable (fun p : (ℝ × ℝ) × ((Fin (outerPilotRounds m) → Fin n → ℝ) × Transcript n) =>
      (p.1,((decodedReservoir p.2.2 : Reservoir n (outerPilotRounds m)),p.2.1))) :=
    measurable_fst.prodMk (((measurable_decodedReservoir.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)))
  convert (measurable_outerPilotValue (n:=n) m hm).comp hInput using 1
  funext p
  rfl

lemma outerPilotFromTranscript_actual (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ)
    (tags : Fin (outerPilotRounds m) → Fin n → ℝ) (y : Reservoir n (outerPilotRounds m)) :
    outerPilotFromTranscript m hm t tags (trainingTranscript (requestAll (outerPilotRounds m)) tags y)=outerPilotValue m hm t (y,tags) := by
  unfold outerPilotFromTranscript
  rw [decodedReservoir_trainingTranscript]

lemma outerPilot_hardBudget (m : ℕ) (tags : Fin (outerPilotRounds m) → Fin n → ℝ)
    (y : Reservoir n (outerPilotRounds m)) (i : Fin n) :
    requests (trainingTranscript (requestAll (outerPilotRounds m)) tags y) i≤outerPilotRounds m := trainingTranscript_budget _ _ _ _

end ProphetSecretary.Statistics.Calibration
