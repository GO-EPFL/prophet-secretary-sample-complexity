import ProphetSecretary.Statistics.ResponseTrainingSplit
import ProphetSecretary.Probability.FiniteObservedSelection
import ProphetSecretary.Model.LearnerConditioning

/-!
# Exact expectation of actual finitely selected response values

The selector uses the preliminary sample. Fresh response samples and the chosen
response seed have their genuine independent laws by the explicit projections.
The value functions may be any measurable integrable response observables; a
separate response guarantee remains an explicit input to subsequent assembly.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n h d : ℕ} {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def finiteResponseValue (s : ((Fin n × Fin h) → ℝ) → ι) (L : ι → Learner n d)
    (f : (c : ι) → Reservoir n d × (L c).Seed → ℝ) (p : Reservoir n (h+d) × FiniteResponseSeeds L) : ℝ :=
  f (s (preliminaryTrainingArray p.1)) (responseTrainingReservoir p.1,p.2 (s (preliminaryTrainingArray p.1)))

/-- No independence hypothesis remains: both integrability and the exact mean are
proved for the actual training reservoir and common independent seed product. -/
theorem finiteResponseValue_integrable_and_integral (P : Instance n)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d)
    {f : (c : ι) → Reservoir n d × (L c).Seed → ℝ}
    (hf : ∀ c, Measurable (f c))
    (hfI : ∀ c, Integrable (f c) ((P.reservoirLaw d).prod (L c).seedLaw)) :
    Integrable (finiteResponseValue s L f) ((P.reservoirLaw (h+d)).prod (finiteResponseSeedLaw L)) ∧
    (∫ p, finiteResponseValue s L f p ∂(P.reservoirLaw (h+d)).prod (finiteResponseSeedLaw L))=
      ∑ c, (P.trainingCoordinateLaw h).real {a | s a=c}*
        (∫ p, f c p ∂(P.reservoirLaw d).prod (L c).seedLaw) :=
  finiteSelectedValue_integrable_and_integral _ (P.trainingCoordinateLaw h)
    (fun c => (P.reservoirLaw d).prod (L c).seedLaw) (fun c => fixedResponseInput_measurePreserving P L c h) hs hf hfI

lemma finiteResponseLearner_frozen_reward (P : Instance n)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d)
    (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L) :
    ((finiteResponseLearner s hs L).frozenRandomizedPolicy y r).expectedReward P=
      ((L (s (preliminaryTrainingArray y))).frozenRandomizedPolicy
        (responseTrainingReservoir y) (r (s (preliminaryTrainingArray y)))).expectedReward P := by
  change (∫ ω : World n Unit, ((finiteResponseLearner s hs L).frozenRule y r).reward
    ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))=_
  rw [finiteResponseLearner_frozen_eq]
  rfl

lemma finiteResponseLearner_frozen_duration (P : Instance n)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d)
    (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L) :
    ((finiteResponseLearner s hs L).frozenRandomizedPolicy y r).expectedDuration P=
      ((L (s (preliminaryTrainingArray y))).frozenRandomizedPolicy
        (responseTrainingReservoir y) (r (s (preliminaryTrainingArray y)))).expectedDuration P := by
  change (∫ ω : World n Unit, ((finiteResponseLearner s hs L).frozenRule y r).stoppingTime
    ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))=_
  rw [finiteResponseLearner_frozen_eq]
  rfl

/-- Expected reward of the actual patched learner is the mixture of the actual
response learners' rewards, with the probabilities of the observable selector. -/
theorem finiteResponseLearner_expectedReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d) :
    (finiteResponseLearner s hs L).expectedReward P=
      ∑ c, (P.trainingCoordinateLaw h).real {a | s a=c}*(L c).expectedReward P := by
  let f := fun (c : ι) (p : Reservoir n d × (L c).Seed) =>
    ((L c).frozenRandomizedPolicy p.1 p.2).expectedReward P
  have hMean := finiteResponseValue_integrable_and_integral P s hs L
    (fun c => (L c).measurable_frozenExpectedReward P)
    (fun c => (L c).integrable_frozenExpectedReward P hP ((P.reservoirLaw d).prod (L c).seedLaw))
  have hEq : (fun p : Reservoir n (h+d) × FiniteResponseSeeds L =>
      ((finiteResponseLearner s hs L).frozenRandomizedPolicy p.1 p.2).expectedReward P)=finiteResponseValue s L f := by
    funext p
    exact finiteResponseLearner_frozen_reward P s hs L p.1 p.2
  have hOuter := (finiteResponseLearner s hs L).integral_frozenExpectedReward P hP
    ((P.reservoirLaw (h+d)).prod (finiteResponseLearner s hs L).seedLaw)
  change (∫ p : Reservoir n (h+d) × FiniteResponseSeeds L,
    ((finiteResponseLearner s hs L).frozenRandomizedPolicy p.1 p.2).expectedReward P
    ∂(P.reservoirLaw (h+d)).prod (finiteResponseSeedLaw L))=(finiteResponseLearner s hs L).expectedReward P at hOuter
  rw [hEq] at hOuter
  rw [←hOuter,hMean.2]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact (L c).integral_frozenExpectedReward P hP ((P.reservoirLaw d).prod (L c).seedLaw)

/-- Physical expected duration obeys the same exact selection mixture. -/
theorem finiteResponseLearner_expectedDuration (P : Instance n)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d) :
    (finiteResponseLearner s hs L).meanDuration P=
      ∑ c, (P.trainingCoordinateLaw h).real {a | s a=c}*(L c).meanDuration P := by
  let f := fun (c : ι) (p : Reservoir n d × (L c).Seed) =>
    ((L c).frozenRandomizedPolicy p.1 p.2).expectedDuration P
  have hMean := finiteResponseValue_integrable_and_integral P s hs L
    (fun c => (L c).measurable_frozenExpectedDuration P)
    (fun c => (L c).integrable_frozenExpectedDuration P ((P.reservoirLaw d).prod (L c).seedLaw))
  have hEq : (fun p : Reservoir n (h+d) × FiniteResponseSeeds L =>
      ((finiteResponseLearner s hs L).frozenRandomizedPolicy p.1 p.2).expectedDuration P)=finiteResponseValue s L f := by
    funext p
    exact finiteResponseLearner_frozen_duration P s hs L p.1 p.2
  have hOuter := (finiteResponseLearner s hs L).integral_frozenExpectedDuration P
    ((P.reservoirLaw (h+d)).prod (finiteResponseLearner s hs L).seedLaw)
  change (∫ p : Reservoir n (h+d) × FiniteResponseSeeds L,
    ((finiteResponseLearner s hs L).frozenRandomizedPolicy p.1 p.2).expectedDuration P
    ∂(P.reservoirLaw (h+d)).prod (finiteResponseSeedLaw L))=(finiteResponseLearner s hs L).meanDuration P at hOuter
  rw [hEq] at hOuter
  rw [←hOuter,hMean.2]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact (L c).integral_frozenExpectedDuration P ((P.reservoirLaw d).prod (L c).seedLaw)

end ProphetSecretary.Statistics
