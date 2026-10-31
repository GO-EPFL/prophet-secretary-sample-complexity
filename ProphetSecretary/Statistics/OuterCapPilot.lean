import ProphetSecretary.Statistics.OuterPilotConditioning
import ProphetSecretary.Model.OuterPilotScale
import ProphetSecretary.Model.OuterFirstPositive

/-!
# The cap-pilot lemma for actual independent tagged training rounds

For each fixed outer cutoff the pilot is a measurable statistic of exactly q_m
fresh raw rounds and free tags. The good event has probability at least 1−1/m;
its zero and positive branches give all reward/scale conclusions of
`upouter:cap-pilot`. `outerPilot_conditional_success` additionally supplies the
actual conditional-probability statement for any preceding independent cutoff.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def outerPilotGoodAt (P : Instance n) (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ) : Set (OuterPilotInputs n m) :=
  {p | (P.retainedMaximumLaw t).real (Ioi (outerPilotValue m hm t p))≤3/1000 ∧
    1/1000≤(P.retainedMaximumLaw t).real (Ici (outerPilotValue m hm t p))}

lemma measurableSet_outerPilotGoodAt (P : Instance n) (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ) :
    MeasurableSet (outerPilotGoodAt P m hm t) := by
  have hInput : Measurable (fun p : OuterPilotInputs n m => (t,taggedTrainingRows p.1 p.2)) :=
    measurable_const.prodMk (measurable_taggedTrainingRows (n:=n) (q:=outerPilotRounds m))
  exact (measurableSet_outerPilotTaggedGood P m hm).preimage hInput

lemma outerPilotGoodAt_probability (P : Instance n) (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ) :
    1-1/(m:ℝ)≤(outerPilotInputsLaw P m).real (outerPilotGoodAt P m hm t) := by
  have hMP : MeasurePreserving (fun p : OuterPilotInputs n m => retainedPilotSamples t (taggedTrainingRows p.1 p.2))
      (outerPilotInputsLaw P m) (Measure.pi (fun _ : Fin (outerPilotRounds m) => P.retainedMaximumLaw t)) := by
    simpa only [Function.comp_def,outerPilotInputsLaw] using (retainedPilotSamples_measurePreserving P (outerPilotRounds m) t).comp
      (taggedTrainingRows_measurePreserving P (outerPilotRounds m))
  have hS := measurableSet_numericalPilotSuccess (P.retainedMaximumLaw t) (outerPilotRank m) (outerPilotRank_pos hm)
  have hProb := map_measureReal_apply (μ:=outerPilotInputsLaw P m) hMP.measurable hS
  rw [hMP.map_eq] at hProb
  have hSet : (fun p : OuterPilotInputs n m => retainedPilotSamples t (taggedTrainingRows p.1 p.2)) ⁻¹'
      numericalPilotSuccess (P.retainedMaximumLaw t) (outerPilotRank m) (outerPilotRank_pos hm)=outerPilotGoodAt P m hm t := rfl
  rw [hSet] at hProb
  exact (outerPilot_success_probability (P.retainedMaximumLaw t) hm).trans_eq hProb

/-- Literal source confidence event with both strict and closed tails visible. -/
theorem outer_cap_pilot_confidence (P : Instance n) (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ) :
    1-1/(m:ℝ)≤(outerPilotInputsLaw P m).real
      {p | (P.retainedMaximumLaw t).real (Ioi (outerPilotValue m hm t p))≤3/1000 ∧
        1/1000≤(P.retainedMaximumLaw t).real (Ici (outerPilotValue m hm t p))} :=
  outerPilotGoodAt_probability P m hm t

/-- All deterministic branches on the actual good pilot event. -/
lemma outerPilotGoodAt_consequences (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ) (p : OuterPilotInputs n m) (hp : p∈outerPilotGoodAt P m hm t) :
    let B : ℝ≥0 := ⟨outerPilotValue m hm t p,outerPilotValue_nonnegative m hm t p⟩
    ((B:ℝ)=0 ∧ (997/1000:ℝ)*(P.retainedAtTag t).expectedMaximum≤
      (firstPositivePolicy n).expectedReward (P.retainedAtTag t)) ∨
    (0<(B:ℝ) ∧ 1/1000000≤((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum/(Instance.outerPilotCap B:ℝ) ∧
      ((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum/(Instance.outerPilotCap B:ℝ)≤1/250 ∧
      (P.retainedAtTag t).valuesLaw.real {x | (Instance.outerPilotCap B:ℝ)≤Instance.maximum x}≤3/1000 ∧
      (Instance.outerPilotCap B:ℝ)≤1000000*((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum ∧
      1000000*((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum≤1000000*(P.retainedAtTag t).expectedMaximum) := by
  let B : ℝ≥0 := ⟨outerPilotValue m hm t p,outerPilotValue_nonnegative m hm t p⟩
  have hRet := P.retainedAtTag_integrable_maximum hP t
  have hStrict : (P.retainedAtTag t).valuesLaw.real {x | (B:ℝ)<Instance.maximum x}≤3/1000 := by
    have h := hp.1
    rw [P.retainedMaximumLaw_Ioi_values] at h
    exact h
  have hClosed : 1/1000≤(P.retainedAtTag t).valuesLaw.real {x | (B:ℝ)≤Instance.maximum x} := by
    have h := hp.2
    rw [P.retainedMaximumLaw_Ici_values] at h
    exact h
  by_cases hB : (B:ℝ)=0
  · refine Or.inl ⟨hB,?_⟩
    rw [hB] at hStrict
    exact firstPositivePolicy_reward_ge_retained_fraction (P.retainedAtTag t) hRet hStrict
  · have hPos : 0<(B:ℝ) := lt_of_le_of_ne B.property (Ne.symm hB)
    exact Or.inr ⟨hPos,(P.retainedAtTag t).capPilot_scale_bounds hRet B hPos hStrict hClosed⟩

/-- `upouter:cap-pilot`, including its actual fresh-sample experiment and hard
per-distribution budget on every pilot outcome. -/
theorem outer_cap_pilot (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (t : ℝ × ℝ) :
    ∃ G : Set (OuterPilotInputs n m), MeasurableSet G ∧
      1-1/(m:ℝ)≤(outerPilotInputsLaw P m).real G ∧
      (∀ p∈G, (P.retainedMaximumLaw t).real (Ioi (outerPilotValue m hm t p))≤3/1000 ∧
        1/1000≤(P.retainedMaximumLaw t).real (Ici (outerPilotValue m hm t p))) ∧
      (∀ p∈G,
        let B : ℝ≥0 := ⟨outerPilotValue m hm t p,outerPilotValue_nonnegative m hm t p⟩
        ((B:ℝ)=0 ∧ (997/1000:ℝ)*(P.retainedAtTag t).expectedMaximum≤
          (firstPositivePolicy n).expectedReward (P.retainedAtTag t)) ∨
        (0<(B:ℝ) ∧ 1/1000000≤((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum/(Instance.outerPilotCap B:ℝ) ∧
          ((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum/(Instance.outerPilotCap B:ℝ)≤1/250 ∧
          (P.retainedAtTag t).valuesLaw.real {x | (Instance.outerPilotCap B:ℝ)≤Instance.maximum x}≤3/1000 ∧
          (Instance.outerPilotCap B:ℝ)≤1000000*((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum ∧
          1000000*((P.retainedAtTag t).cap (Instance.outerPilotCap B)).expectedMaximum≤1000000*(P.retainedAtTag t).expectedMaximum)) ∧
      (∀ p : OuterPilotInputs n m, ∀ i : Fin n,
        requests (trainingTranscript (requestAll (outerPilotRounds m)) p.2 p.1) i≤outerPilotRounds m) := by
  exact ⟨outerPilotGoodAt P m hm t,measurableSet_outerPilotGoodAt P m hm t,outerPilotGoodAt_probability P m hm t,
    (fun _ hp => hp),(fun p hp => outerPilotGoodAt_consequences P hP m hm t p hp),(fun p i => outerPilot_hardBudget m p.2 p.1 i)⟩

end ProphetSecretary.Statistics
