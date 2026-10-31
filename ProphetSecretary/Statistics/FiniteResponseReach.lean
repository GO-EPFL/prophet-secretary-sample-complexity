import ProphetSecretary.Statistics.FiniteResponseValues
import ProphetSecretary.Model.LearnerReachConditioning

/-!
# Exact reach probability for a finitely patched learner

The same actual past/fresh-data split applies to reach indicators. This is an
identity for arbitrary admissible response policies and does not invoke the
threshold-only comparison between reach and expected duration.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n h d : ℕ} {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finiteResponseLearner_frozen_reach (P : Instance n)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d)
    (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L) (i : Fin n) :
    ((finiteResponseLearner s hs L).frozenRule y r).reachProbability P (Measure.dirac ()) i=
      ((L (s (preliminaryTrainingArray y))).frozenRule
        (responseTrainingReservoir y) (r (s (preliminaryTrainingArray y)))).reachProbability P (Measure.dirac ()) i := by
  rw [finiteResponseLearner_frozen_eq]

/-- The true online reach probability is exactly the observed selection mixture
of the true online reach probabilities of the actual response learners. -/
theorem finiteResponseLearner_reachProbability (P : Instance n)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d) (i : Fin n) :
    (finiteResponseLearner s hs L).reachProbability P i=
      ∑ c, (P.trainingCoordinateLaw h).real {a | s a=c}*(L c).reachProbability P i := by
  let f := fun (c : ι) (p : Reservoir n d × (L c).Seed) =>
    ((L c).frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i
  have hMean := finiteResponseValue_integrable_and_integral P s hs L
    (fun c => (L c).measurable_frozenReachProbability P i)
    (fun c => (L c).integrable_frozenReachProbability P ((P.reservoirLaw d).prod (L c).seedLaw) i)
  have hEq : (fun p : Reservoir n (h+d) × FiniteResponseSeeds L =>
      ((finiteResponseLearner s hs L).frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i)=finiteResponseValue s L f := by
    funext p
    exact finiteResponseLearner_frozen_reach P s hs L p.1 p.2 i
  have hOuter := (finiteResponseLearner s hs L).integral_frozenReachProbability P
    ((P.reservoirLaw (h+d)).prod (finiteResponseLearner s hs L).seedLaw) i
  change (∫ p : Reservoir n (h+d) × FiniteResponseSeeds L,
    ((finiteResponseLearner s hs L).frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i
    ∂(P.reservoirLaw (h+d)).prod (finiteResponseSeedLaw L))=(finiteResponseLearner s hs L).reachProbability P i at hOuter
  rw [hEq] at hOuter
  rw [←hOuter,hMean.2]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact (L c).integral_frozenReachProbability P ((P.reservoirLaw d).prod (L c).seedLaw) i

end ProphetSecretary.Statistics
