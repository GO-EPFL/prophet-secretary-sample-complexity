import ProphetSecretary.Limiting.GeneralFiniteArrayEvaluation
import ProphetSecretary.Limiting.HybridBranchLaw
import ProphetSecretary.Limiting.HybridCutoffPayoff
import ProphetSecretary.Limiting.ThresholdedOfferFamily

/-!
# Actual finite coarse execution and its high-point observable

A shared hybrid callback is deployed on arbitrary independent virtual offer
laws. It keeps retained identities and filters only anonymous strict-past
marks. Its actual finite reward and duration equal the corresponding
label-free high-point observable on the constructed product law.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

noncomputable def RandomizedHybridPolicy.above (π : RandomizedHybridPolicy n) (d : ℝ) : RandomizedHybridPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.above d
  measurable_rule := π.rule.above_measurable π.measurable_rule d

noncomputable def RandomizedHybridPolicy.finiteCutoffEvaluation (π : RandomizedHybridPolicy n)
    (N : ℕ) (d : ℝ) : Model.RandomizedPolicy (n+N) := (π.above d).finiteEvaluation N

lemma configurationAbove_eq_thresholdedArray (d : ℝ) (v : Fin N → Point) :
    configurationAbove d (configurationMk N v)=
      ProphetSecretary.Probability.finiteMeasureOrZero (thresholdedOfferCountingMeasure d v) := by
  unfold configurationAbove
  have he : (countingMeasure (configurationMk N v)).restrict (univ ×ˢ Ioi d)=
      thresholdedOfferCountingMeasure d v := by
    rw [restricted_countingMeasure _ (MeasurableSet.univ.prod measurableSet_Ioi)]
    rfl
  rw [he]

noncomputable def finiteCutoffObserver {Seed : Type*} (d : ℝ)
    (v : (Fin N → Point) × Model.World n Seed) : FiniteObserverWorld n Seed :=
  (ProphetSecretary.Probability.finiteMeasureOrZero (thresholdedOfferCountingMeasure d v.1),v.2)

lemma measurable_finiteCutoffObserver {Seed : Type*} [MeasurableSpace Seed] (d : ℝ) :
    Measurable (finiteCutoffObserver (n := n) (N := N) (Seed := Seed) d) := by
  have hM : Measurable (thresholdedOfferCountingMeasure (ι := Fin N) d) :=
    Finset.measurable_fun_sum _ (fun i _ =>
      (measurable_observedSingleton (MeasurableSet.univ.prod measurableSet_Ioi)).comp (measurable_pi_apply i))
  exact (ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp (hM.comp measurable_fst)).prodMk measurable_snd

lemma RandomizedHybridPolicy.finiteCutoffEvaluation_payoffs_eq_observable_ae
    (π : RandomizedHybridPolicy n) (P : Model.Instance n) (Q : Model.Instance N) (d : ℝ) :
    ∀ᵐ v ∂(Measure.pi (fun j : Fin N => Model.Instance.uniformClock.prod (Q.law j))).prod (P.worldLaw π.seedLaw),
      (π.finiteCutoffEvaluation N d).realizedReward
        (combinedValues v.2.1 v.1,(combinedClocks v.2.2.1 v.1,v.2.2.2))=
        π.rule.observableReward 0 (finiteCutoffObserver d v) ∧
      (π.finiteCutoffEvaluation N d).realizedDuration
        (combinedValues v.2.1 v.1,(combinedClocks v.2.2.1 v.1,v.2.2.2))=
        π.rule.observableDuration (finiteCutoffObserver d v) := by
  have hMP := generalFiniteArrayWorld_measurePreserving P Q π.seedLaw
  have hValues : ∀ᵐ ω ∂(P.appendIndependent Q).worldLaw π.seedLaw, ∀ k, 0≤ω.1 k :=
    (measurePreserving_fst : MeasurePreserving (fun ω : Model.World (n+N) π.Seed => ω.1)
      ((P.appendIndependent Q).worldLaw π.seedLaw) (P.appendIndependent Q).valuesLaw).quasiMeasurePreserving.ae
      (P.appendIndependent Q).ae_nonnegative
  filter_upwards [hMP.quasiMeasurePreserving.ae hValues,
    hMP.quasiMeasurePreserving.ae ((P.appendIndependent Q).world_clocks_distinct π.seedLaw),
    hMP.quasiMeasurePreserving.ae ((P.appendIndependent Q).world_clocks_mem_unitInterval π.seedLaw)] with v hV hInj hTimes
  have hObs : hybridObserverAbove d (configurationMk N v.1,v.2)=finiteCutoffObserver d v := by
    unfold hybridObserverAbove finiteCutoffObserver
    rw [configurationAbove_eq_thresholdedArray]
  constructor
  · change ((π.above d).finiteEvaluation N).realizedReward
      (combinedValues v.2.1 v.1,(combinedClocks v.2.2.1 v.1,v.2.2.2))=_
    rw [RandomizedHybridPolicy.finiteEvaluation_reward]
    change (π.rule.above d).realizedReward 0 (configurationMk N v.1,v.2)=_
    rw [← π.rule.above_reward_eq_observable π.measurable_rule d (configurationMk N v.1,v.2)
      hTimes hV hInj 0,hObs]
  · change ((π.above d).finiteEvaluation N).realizedDuration
      (combinedValues v.2.1 v.1,(combinedClocks v.2.2.1 v.1,v.2.2.2))=_
    rw [RandomizedHybridPolicy.finiteEvaluation_duration]
    change (π.rule.above d).realizedDuration (configurationMk N v.1,v.2)=_
    rw [← π.rule.above_duration_eq_observable π.measurable_rule d (configurationMk N v.1,v.2) hTimes,hObs]
end ProphetSecretary.Limiting
