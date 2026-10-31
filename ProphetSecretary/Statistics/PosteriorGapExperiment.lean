import ProphetSecretary.Statistics.FinitePriorTrainingObservation
import ProphetSecretary.Statistics.PosteriorGapBounds

/-!
# The posterior gap under the actual joint experiment

The prior-weighted prefix-law definition equals the expectation with the
hidden true atom retained analytically. The observable bounded posterior
agrees almost surely with the conditional-expectation version. This permits
pointwise scalar inequalities to be integrated without giving the atom or
any unused training column to the policy.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def posteriorGapKernel (F : FinitePrior n) (N b k : ℕ)
    (p : Fin F.size × Reservoir n (trainingLength N b k)) : ℝ :=
  normalizedScalarGap (F.offerInstance p.1)
    (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.2))

lemma measurable_posteriorGapKernel (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) : Measurable (F.posteriorGapKernel N b k) := by
  let W := fun p : Fin F.size × Reservoir n (trainingLength N b k) =>
    F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.2)
  have hm : Measurable W := (F.measurable_boundedPosteriorFromObservation N b k).comp
    ((measurable_extendTrainingPrefix n N b k).comp measurable_snd)
  have hr (p) : W p∈Icc (0 : ℝ) 1 := F.boundedPosteriorFromObservation_mem_unit N b k _
  exact measurable_countable_choice measurable_fst (fun θ =>
    (F.offerInstance θ).measurable_normalizedGap_of_weight
      ((F.offerInstance θ).integrable_maximum_of_bounded (hcap θ)) hm hr)

theorem integral_observedPosteriorGap_eq_expected (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) :
    (∫ ω, normalizedScalarGap (F.offerInstance ω.1)
      (F.boundedPosteriorFromObservation N b k (F.observe N b k ω)) ∂F.law N)=
      F.expectedPosteriorGap N b k := by
  let c := trainingLength N b k
  let g := F.posteriorGapKernel N b k
  have hg := F.measurable_posteriorGapKernel N b k hcap
  have hInt : Integrable g (F.trainingPriorLaw c) := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by
      have h := (F.offerInstance p.1).normalizedScalarGap_mem_unit (hcap p.1)
        (F.boundedPosteriorFromObservation_mem_unit N b k (extendTrainingPrefix n N b k p.2))
      change ‖normalizedScalarGap (F.offerInstance p.1)
        (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.2))‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg h.1]
      exact h.2))
  have hMean := (F.priorTrainingObservation_measurePreserving N b k).hasLaw.integral_comp hg.aestronglyMeasurable
  calc
    _ = ∫ ω, g (F.priorTrainingObservation N b k ω) ∂F.law N := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by
        change _=normalizedScalarGap (F.offerInstance ω.1)
          (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k (F.observedTraining N b k ω)))
        rw [F.extend_observedTraining_eq])
    _ = ∫ p, g p ∂F.trainingPriorLaw c := hMean
    _ = _ := by
      rw [F.integral_trainingPriorLaw c hg hInt]
      unfold expectedPosteriorGap
      apply Finset.sum_congr rfl
      intro θ _
      congr 1
      have hFirst : MeasurePreserving (Prod.fst : Reservoir n c × Unit → Reservoir n c)
          (((F.offerInstance θ).reservoirLaw c).prod (Measure.dirac ())) ((F.offerInstance θ).reservoirLaw c) :=
        measurePreserving_fst
      have hData : Measurable (fun y : Reservoir n c => g (θ,y)) :=
        hg.comp (measurable_const.prodMk measurable_id)
      exact (hFirst.hasLaw.integral_comp hData.aestronglyMeasurable).symm

theorem integral_posteriorGap_eq_expected (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) :
    (∫ ω, normalizedScalarGap (F.offerInstance ω.1) (F.posterior N b k ω) ∂F.law N)=
      F.expectedPosteriorGap N b k := by
  apply Eq.trans _ (F.integral_observedPosteriorGap_eq_expected N b k hcap)
  apply integral_congr_ae
  exact (F.boundedPosterior_observed_eq_ae N b k).mono (fun ω h =>
    congrArg (normalizedScalarGap (F.offerInstance ω.1)) h.symm)

end ProphetSecretary.Statistics.FinitePrior
