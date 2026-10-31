import ProphetSecretary.Statistics.FinitePriorGameExpectation
import ProphetSecretary.Model.SelectedScoreConditioning

/-!
# Integrating an observable current score over the online instance

The current weight is a function of visible training data. The actual
prefix execution map and selected-weight Fubini identity identify its
score with the frozen scalar objective under each true prior atom. The
hidden target and a hypothetical next observation are not policy inputs.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

def visiblePrefixWeight (n N b k : ℕ) (A : ValueArray n N → ℝ)
    (p : Reservoir n (trainingLength N b k) × Seed) : ℝ :=
  A (extendTrainingPrefix n N b k p.1)

lemma measurable_visiblePrefixWeight (N b k : ℕ) {A : ValueArray n N → ℝ} (hA : Measurable A) :
    Measurable (visiblePrefixWeight (Seed:=Seed) n N b k A) :=
  hA.comp ((measurable_extendTrainingPrefix n N b k).comp measurable_fst)

lemma integral_observableScore_atom (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size)
    (hP : Integrable Instance.maximum (F.offerInstance θ).valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (A : ValueArray n N → ℝ) (hA : Measurable A) (hRange : ∀ d, A d∈Icc (0 : ℝ) 1) (C : ℝ) :
    (∫ z : ValueArray n N × ((Fin n → ℝ) × Seed),
      F.onlineGameScore N b k π C (fun ω => A (F.observe N b k ω)) ((θ,z.1),z.2)
      ∂((F.offerInstance θ).trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) =
    ∫ p : Reservoir n (trainingLength N b k) × Seed,
      ((prefixLearner N b k ν π hπ).frozenRandomizedPolicy p.1 p.2).scalarObjective (F.offerInstance θ)
        (A (extendTrainingPrefix n N b k p.1)) (1-A (extendTrainingPrefix n N b k p.1))-
      C*(A (extendTrainingPrefix n N b k p.1)*(F.offerInstance θ).expectedMaximum+
        1-A (extendTrainingPrefix n N b k p.1))
      ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod ν := by
  let P := F.offerInstance θ
  let L := prefixLearner N b k ν π hπ
  let W := visiblePrefixWeight (Seed:=Seed) n N b k A
  have hW : Measurable W := measurable_visiblePrefixWeight N b k hA
  have hUnit (p) : W p∈Icc (0 : ℝ) 1 := hRange (extendTrainingPrefix n N b k p.1)
  have hMP := prefixExecutionWorld_measurePreserving P N b k ν
  have hMean := hMP.hasLaw.integral_comp (L.measurable_selectedScore hW C).aestronglyMeasurable
  let D : Measure (Reservoir n (trainingLength N b k) × Seed) := (P.reservoirLaw (trainingLength N b k)).prod ν
  have hProbD : IsProbabilityMeasure D := by dsimp only [D];infer_instance
  have hFrozen := @Learner.integral_selectedScore_eq_frozen n (trainingLength N b k) L P hP D hProbD W hW hUnit C
  have hPoint (z : ValueArray n N × ((Fin n → ℝ) × Seed)) :
      F.onlineGameScore N b k π C (fun ω => A (F.observe N b k ω)) ((θ,z.1),z.2)=
        L.selectedScore W C (prefixExecutionWorld n N b k z) := by
    have hSource := F.onlineGameScore_eq_mixture N b k π C
      (fun ω => A (F.observe N b k ω)) ((θ,z.1),z.2)
    have hWorld : prefixExecutionWorld n N b k z=
        (F.onlineValues (θ,z.1),(z.2.1,(F.observedTraining N b k (θ,z.1),z.2.2))) :=
      F.prefixExecutionWorld_eq_observed N b k (θ,z.1) z.2.1 z.2.2
    have hScoreWorld := congrArg (fun q : World n (Reservoir n (trainingLength N b k) × Seed) => L.selectedScore W C q) hWorld
    have hCoeff : W (F.observedTraining N b k (θ,z.1),z.2.2)=A (F.observe N b k (θ,z.1)) :=
      congrArg A (F.extend_observedTraining_eq N b k (θ,z.1))
    have hR := F.prefixLearner_reward_eq_observed N b k ν π hπ (θ,z.1) z.2.1 z.2.2
    have hT := F.prefixLearner_duration_eq_observed N b k ν π hπ (θ,z.1) z.2.1 z.2.2
    have hPayoff := congrArg₂
      (fun q : ℝ => fun rt : ℝ × ℝ => q*(rt.1-C*Instance.maximum (F.onlineValues (θ,z.1)))+(1-q)*(rt.2-C))
      hCoeff.symm (congrArg₂ Prod.mk hR.symm hT.symm)
    exact hSource.trans (hPayoff.trans hScoreWorld.symm)
  have hIntegral := integral_congr_ae
    (μ:=((P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)))
    (Eventually.of_forall hPoint)
  exact hIntegral.trans (hMean.trans hFrozen)

theorem integral_observableScore_eq_frozen_average (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (A : ValueArray n N → ℝ) (hA : Measurable A) (hRange : ∀ d, A d∈Icc (0 : ℝ) 1)
    {C : ℝ} (hC : C∈Icc (0 : ℝ) 1) :
    (∫ w, F.onlineGameScore N b k π C (fun ω => A (F.observe N b k ω)) w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)) =
    ∑ θ : Fin F.size, (F.weight θ : ℝ)*
      (∫ p : Reservoir n (trainingLength N b k) × Seed,
        ((prefixLearner N b k ν π hπ).frozenRandomizedPolicy p.1 p.2).scalarObjective (F.offerInstance θ)
          (A (extendTrainingPrefix n N b k p.1)) (1-A (extendTrainingPrefix n N b k p.1))-
        C*(A (extendTrainingPrefix n N b k p.1)*(F.offerInstance θ).expectedMaximum+
          1-A (extendTrainingPrefix n N b k p.1))
        ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod ν) := by
  have hWeight := hA.comp (F.measurable_observe N b k)
  have hInt := F.onlineGameScore_integrable N b k hcap ν π hπ hC hWeight
    (Eventually.of_forall (fun ω => hRange (F.observe N b k ω)))
  have hMeas : Measurable (F.onlineGameScore N b k π C (fun ω => A (F.observe N b k ω))) :=
    (F.measurable_onlinePayoff N b k (measurable_gameBaseline N hπ C)).add
      ((hWeight.comp measurable_fst).mul (F.measurable_onlinePayoff N b k (measurable_gameFactor N hπ C)))
  rw [F.integral_auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν) hMeas hInt]
  apply Finset.sum_congr rfl
  intro θ _
  rw [F.integral_observableScore_atom N b k θ ((F.offerInstance θ).integrable_maximum_of_bounded (hcap θ))
    ν π hπ A hA hRange C]

theorem integral_currentPosteriorScore_eq_frozen_average (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) {C : ℝ} (hC : C∈Icc (0 : ℝ) 1) :
    (∫ w, F.onlineGameScore N b k π C (F.posterior N b k) w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)) =
    ∑ θ : Fin F.size, (F.weight θ : ℝ)*
      (∫ p : Reservoir n (trainingLength N b k) × Seed,
        ((prefixLearner N b k ν π hπ).frozenRandomizedPolicy p.1 p.2).scalarObjective (F.offerInstance θ)
          (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
          (1-F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))-
        C*(F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)*(F.offerInstance θ).expectedMaximum+
          1-F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
        ∂((F.offerInstance θ).reservoirLaw (trainingLength N b k)).prod ν) := by
  apply Eq.trans _ (F.integral_observableScore_eq_frozen_average N b k hcap ν π hπ
    (F.boundedPosteriorFromObservation N b k) (F.measurable_boundedPosteriorFromObservation N b k)
    (F.boundedPosteriorFromObservation_mem_unit N b k) hC)
  apply integral_congr_ae
  have hFirst : MeasurePreserving (Prod.fst : BaseWorld F N × ((Fin n → ℝ) × Seed) → BaseWorld F N)
      (F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)) (F.law N) := measurePreserving_fst
  filter_upwards [hFirst.quasiMeasurePreserving.ae (F.boundedPosterior_observed_eq_ae N b k)] with w hw
  unfold onlineGameScore
  exact congrArg (fun t : ℝ => F.onlinePayoff N b k (gameBaseline N π C) w+
    t*F.onlinePayoff N b k (gameFactor N π C) w) hw.symm

end ProphetSecretary.Statistics.FinitePrior
