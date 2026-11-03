import ProphetSecretary.Statistics.CalibratedOuter.MarkCoupling
import ProphetSecretary.Probability.FairBitUniform

/-!
# The law of the fair-bit outer marks

The same outer policy can be run from a flat continuous, grid-index,
or fair-bit seed. Product-law transport identifies the grid-index law.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

abbrev OuterMarkArray (n m : ℕ) (K : Type) := Fin (outerMarkSlotCount n m) → K

noncomputable def outerMarkPolicy {E : Type} (hm : 1≤m) (L : Learner n (2*m))
    (decode : E → OuterMarkArray n m ℝ) :
    Policy (Reservoir n (outerSampleBudget m) × (E × L.Seed)) n :=
  (outerPolicy m hm L).pullbackSeed (fun q =>
    (q.1,outerSeedFromMarks L (unpackOuterMarks (decode q.2.1)) q.2.2))

lemma measurable_outerMarkPolicy {E : Type} [MeasurableSpace E]
    (hm : 1≤m) (L : Learner n (2*m))
    (decode : E → OuterMarkArray n m ℝ) (hd : Measurable decode) :
    (outerMarkPolicy hm L decode).IsMeasurable := by
  have hp := (outerSeedFromMarks_measurePreserving L).measurable
  have hu := (measurePreserving_unpackOuterMarks n m).measurable.comp hd
  exact (outerPolicy m hm L).pullbackSeed_measurable (outerPolicy_isMeasurable m hm L)
    (measurable_fst.prodMk (hp.comp ((hu.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))))

noncomputable def outerMarkedLearner {E : Type} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (hm : 1≤m) (L : Learner n (2*m)) (decode : E → OuterMarkArray n m ℝ) (hd : Measurable decode) :
    Learner n (outerSampleBudget m) :=
  Learner.ofComputedSamplePolicy (E × L.Seed) (ν.prod L.seedLaw)
    (outerMarkPolicy hm L decode) (measurable_outerMarkPolicy hm L decode hd)

lemma outerMarkedLearner_decide {E : Type} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (hm : 1≤m) (L : Learner n (2*m)) (decode : E → OuterMarkArray n m ℝ) (hd : Measurable decode)
    (y : Reservoir n (outerSampleBudget m)) (u : E) (s : L.Seed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (outerMarkedLearner ν hm L decode hd).policy.decide (y,(u,s)) t i x H =
      (outerPolicy m hm L).decide (y,outerSeedFromMarks L (unpackOuterMarks (decode u)) s) t i x H :=
  Learner.ofComputedSamplePolicy_decide _ _ _ _ y (u,s) t i x H

lemma outerMarkedLearner_transport {E F : Type} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : 1≤m) (L : Learner n (2*m)) (g : E → F) (hg : MeasurePreserving g μ ν)
    (decode : F → OuterMarkArray n m ℝ) (hd : Measurable decode) (P : Instance n) :
    (outerMarkedLearner μ hm L (decode ∘ g) (hd.comp hg.measurable)).expectedReward P =
      (outerMarkedLearner ν hm L decode hd).expectedReward P := by
  let π := (outerMarkedLearner ν hm L decode hd).randomizedPolicy P
  let ρ := (outerMarkedLearner μ hm L (decode ∘ g) (hd.comp hg.measurable)).randomizedPolicy P
  let mapSeed : ρ.Seed → π.Seed := Prod.map id (Prod.map g id)
  have h := (MeasurePreserving.id (P.reservoirLaw (outerSampleBudget m))).prod
    (hg.prod (MeasurePreserving.id L.seedLaw))
  let σ := π.pullbackSeed ρ.seedLaw mapSeed h.measurable
  have hRule : σ.rule=ρ.rule := by
    apply congrArg Policy.mk
    funext q t i x H
    obtain ⟨y,u,s⟩ := q
    exact (outerMarkedLearner_decide ν hm L decode hd y (g u) s t i x H).trans
      (outerMarkedLearner_decide μ hm L (decode ∘ g) (hd.comp hg.measurable) y u s t i x H).symm
  have hReward : ρ.expectedReward P=σ.expectedReward P := by
    change (∫ ω : ρ.World, ρ.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ρ.seedLaw) =
      ∫ ω : ρ.World, σ.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ρ.seedLaw
    rw [hRule]
    rfl
  exact hReward.trans (π.pullbackSeed_expectedReward ρ.seedLaw mapSeed h.measurable h P)

lemma outerMarkedLearner_uniform_reward (hm : 1≤m) (L : Learner n (2*m)) (P : Instance n) :
    (outerMarkedLearner (Instance.clocksLaw (n*(outerSampleBudget m+1))) hm L id
      measurable_id).expectedReward P = (outerLearner m hm L).expectedReward P := by
  let V := Instance.clocksLaw (outerMarkSlotCount n m)
  letI : IsProbabilityMeasure V := Instance.clocksLaw_probability
  let π := (outerLearner m hm L).randomizedPolicy P
  let ρ := (outerMarkedLearner V hm L id measurable_id).randomizedPolicy P
  let f : ρ.Seed → π.Seed := fun q =>
    (q.1,outerSeedFromMarks L (unpackOuterMarks q.2.1) q.2.2)
  have hUnpack : MeasurePreserving (unpackOuterMarks (n := n) (m := m) (K := ℝ))
      V (outerMarksLaw n m) := measurePreserving_unpackOuterMarks n m
  have hPack := (outerSeedFromMarks_measurePreserving L).comp
    (hUnpack.prod (MeasurePreserving.id L.seedLaw))
  have h : MeasurePreserving f ρ.seedLaw π.seedLaw :=
    (MeasurePreserving.id (P.reservoirLaw (outerSampleBudget m))).prod hPack
  let σ := π.pullbackSeed ρ.seedLaw f h.measurable
  have hRule : σ.rule=ρ.rule := by
    apply congrArg Policy.mk
    funext q t i x H
    obtain ⟨y,u,s⟩ := q
    exact (outerLearner_decide m hm L (y,outerSeedFromMarks L (unpackOuterMarks u) s) t i x H).trans
      (outerMarkedLearner_decide V hm L id measurable_id y u s t i x H).symm
  have hReward : ρ.expectedReward P=σ.expectedReward P := by
    change (∫ ω : ρ.World, ρ.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ρ.seedLaw) =
      ∫ ω : ρ.World, σ.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ρ.seedLaw
    rw [hRule]
    rfl
  exact hReward.trans (π.pullbackSeed_expectedReward ρ.seedLaw f h.measurable h P)

noncomputable def fairMarkDecoder (b : ℕ) (bits : OuterMarkArray n m (Fin b → Bool)) :
    OuterMarkArray n m ℝ := fun j => gridPoint (2^b) (fairBitsIndex b (bits j))

noncomputable def outerFairMarkLearner (hm : 1≤m) (L : Learner n (2*m)) (b : ℕ) :
    Learner n (outerSampleBudget m) :=
  outerMarkedLearner (Measure.pi (fun _ : Fin (n*(outerSampleBudget m+1)) => fairBitVectorLaw b)) hm L
    (fairMarkDecoder b) (measurable_of_countable _)

lemma outerFairMarkLearner_reward_eq_rounded (hm : 1≤m) (L : Learner n (2*m)) (b : ℕ)
    (P : Instance n) :
    (outerFairMarkLearner hm L b).expectedReward P =
      (outerMarkedLearner (Instance.clocksLaw (n*(outerSampleBudget m+1))) hm L
        (fun u i => uniformGridRound (2^b) (by positivity) (u i))
        (measurable_pi_lambda _ (fun i => (measurable_uniformGridRound (2^b) (by positivity)).comp
          (measurable_pi_apply i)))).expectedReward P := by
  let M := n*(outerSampleBudget m+1)
  let decode : (Fin M → Fin (2^b)) → OuterMarkArray n m ℝ := fun u i => gridPoint (2^b) (u i)
  have hd : Measurable decode := measurable_of_countable _
  have hf := outerMarkedLearner_transport _ _ hm L _ (measurePreserving_fairIndexVector M b) decode hd P
  have hc := outerMarkedLearner_transport _ _ hm L _ (measurePreserving_gridIndexVector M (2^b) (by positivity))
    decode hd P
  exact hf.trans hc.symm

end ProphetSecretary.Statistics.Calibration
