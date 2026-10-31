import ProphetSecretary.Limiting.TruncatedAcceptedMeasure
import ProphetSecretary.Limiting.FiniteObserverLaw
import ProphetSecretary.Limiting.CountableTruncatedPolicy
import ProphetSecretary.Limiting.CountableClockNullSets

/-!
# Actual countable truncated payoffs depend only on the allowed observer law

The common finite-observer input is analytical. The accepted-point measure
uses only strict past restrictions for each decision. Actual first-attainment,
clock injectivity, and the accepted-measure identity prove equality of reward
and duration, rather than inferring policy convergence from value convergence.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

variable {N : ℕ} {Seed : Type*}

noncomputable def HybridRule.observableDuration (π : HybridRule N Seed) (v : FiniteObserverWorld N Seed) : ℝ :=
  FirstPoint.time (π.acceptedPointMeasure v : Measure Point)

noncomputable def HybridRule.observableReward (π : HybridRule N Seed) (a : ℝ)
    (v : FiniteObserverWorld N Seed) : ℝ := FirstPoint.reward a (π.acceptedPointMeasure v)

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_observableDuration (π : HybridRule N Seed) (hπ : π.IsMeasurable) :
    Measurable π.observableDuration :=
  FirstPoint.measurable_time.comp (measurable_subtype_coe.comp (π.measurable_acceptedPointMeasure hπ))

lemma HybridRule.measurable_observableReward (π : HybridRule N Seed) (hπ : π.IsMeasurable) (a : ℝ) :
    Measurable (π.observableReward a) :=
  (FirstPoint.measurable_reward a).comp (π.measurable_acceptedPointMeasure hπ)

lemma HybridRule.extended_payoffs_eq_observable (π : HybridRule N Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∀ᵐ v ∂B.completeWorldLaw ν,
      π.observableDuration (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v) =
        (extendTruncatedRule π b).realizedDuration v ∧
      π.observableReward B.terminal (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v) =
        (extendTruncatedRule π b).realizedReward B.terminal v := by
  have hfinite := (Measure.quasiMeasurePreserving_fst (μ := B.bandConfigurationsLaw)
    (ν := B.individualWorldLaw ν)).ae (B.finiteCutoffCountingMeasure_coe_ae hb)
  have hadm := extendTruncatedRule_admissible B π ν hb
  filter_upwards [hfinite,hadm,B.present_candidate_times_injective ν,B.codeValue_bounded ν] with v hμ ha hc hx
  let ψ := extendTruncatedRule π b
  let μ := π.acceptedPointMeasure (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)
  have hm : (μ : Measure Point) = FirstAcceptance.pointMeasure ψ.codeAccepted codeTime codeValue v :=
    acceptedPointMeasure_eq_extended_execution π hπ b v _ hμ
  have htimes (i : ℕ) (hi : ψ.codeAccepted v i) : codeTime v i ∈ Icc (0 : ℝ) 1 := hi.2.1
  have hinj : Set.InjOn (codeTime v) {i | ψ.codeAccepted v i} := by
    intro i hi j hj he
    have hci : candidatePresent v (candidateEnumeration.symm i) := hi.1
    have hcj : candidatePresent v (candidateEnumeration.symm j) := hj.1
    have ht : (candidatePoint v (candidateEnumeration.symm i)).1 =
        (candidatePoint v (candidateEnumeration.symm j)).1 := he
    exact candidateEnumeration.symm.injective (hc hci hcj ht)
  constructor
  · change FirstPoint.time (μ : Measure Point) = FirstAcceptance.stoppingTime ψ.codeAccepted codeTime v
    rw [hm]
    exact FirstAcceptance.pointMeasure_time_eq ha htimes
  · exact FirstAcceptance.pointMeasure_reward_eq B.terminal μ hm ha htimes
      (fun i hi => (hx i hi.1).1) hinj

lemma RandomizedHybridPolicy.extended_expectedDuration_observable (π : RandomizedHybridPolicy N)
    (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    (π.extendToCountable B hb).expectedDuration =
      ∫ q, π.rule.observableDuration q ∂finiteObserverLaw (B.individualPrefix N) (B.intensityAbove b hb) π.seedLaw := by
  have hmp := B.finiteObserverProjection_measurePreserving π.seedLaw N hb
  have he := integral_map (μ := B.completeWorldLaw π.seedLaw) hmp.measurable.aemeasurable
    (π.rule.measurable_observableDuration π.measurable_rule).aestronglyMeasurable
  rw [hmp.map_eq] at he
  have hpay := π.rule.extended_payoffs_eq_observable π.measurable_rule B π.seedLaw hb
  change (∫ v, (extendTruncatedRule π.rule b).realizedDuration v ∂B.completeWorldLaw π.seedLaw) = _
  exact (integral_congr_ae (hpay.mono (fun _ h => h.1.symm))).trans he.symm

lemma RandomizedHybridPolicy.extended_expectedReward_observable (π : RandomizedHybridPolicy N)
    (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    (π.extendToCountable B hb).expectedReward =
      ∫ q, π.rule.observableReward B.terminal q ∂finiteObserverLaw (B.individualPrefix N) (B.intensityAbove b hb) π.seedLaw := by
  have hmp := B.finiteObserverProjection_measurePreserving π.seedLaw N hb
  have he := integral_map (μ := B.completeWorldLaw π.seedLaw) hmp.measurable.aemeasurable
    (π.rule.measurable_observableReward π.measurable_rule B.terminal).aestronglyMeasurable
  rw [hmp.map_eq] at he
  have hpay := π.rule.extended_payoffs_eq_observable π.measurable_rule B π.seedLaw hb
  change (∫ v, (extendTruncatedRule π.rule b).realizedReward B.terminal v ∂B.completeWorldLaw π.seedLaw) = _
  exact (integral_congr_ae (hpay.mono (fun _ h => h.2.symm))).trans he.symm

end ProphetSecretary.Limiting
