import ProphetSecretary.Statistics.MixedRankTablePerformance
import Mathlib.Probability.HasLaw

/-!
# Replacing an admissible finite-grid response by an actual table mixture

The table law is the image of the learner's auxiliary seed law, independently
of the unknown instance and its training samples. For a cap-accepting,
zero-rejecting response the two executions agree on all grid observations.
The all-outcome budget of the table learner was proved separately.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def rankLearnerTableLaw (L : RankLearner n k) (G : Finset ℝ) : Measure (RankStrategyTable n k G) :=
  L.seedLaw.map (rankLearnerStrategyTable L G)

instance rankLearnerTableLaw_probability (L : RankLearner n k) (G : Finset ℝ) :
    IsProbabilityMeasure (rankLearnerTableLaw L G) :=
  Measure.isProbabilityMeasure_map (measurable_rankLearnerStrategyTable L G).aemeasurable

noncomputable def rankLearnerTableMixture (L : RankLearner n k) (G : Finset ℝ) : RankLearner n k :=
  mixedRankTableLearner G (rankLearnerTableLaw L G)

abbrev RankLearnerInputWorld (L : RankLearner n k) :=
  (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n k × L.Seed))

noncomputable def rankLearnerInputLaw (L : RankLearner n k) (P : Instance n) : Measure (RankLearnerInputWorld L) :=
  P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw k).prod L.seedLaw))

instance rankLearnerInputLaw_probability (L : RankLearner n k) (P : Instance n) :
    IsProbabilityMeasure (rankLearnerInputLaw L P) := by unfold rankLearnerInputLaw;infer_instance

noncomputable def rankLearnerTableWorldMap (L : RankLearner n k) (G : Finset ℝ)
    (ω : RankLearnerInputWorld L) : MixedRankTableWorld n k G :=
  (ω.1,(ω.2.1,(ω.2.2.1,rankLearnerStrategyTable L G ω.2.2.2)))

lemma rankLearnerTableWorldMap_measurePreserving (L : RankLearner n k) (G : Finset ℝ) (P : Instance n) :
    MeasurePreserving (rankLearnerTableWorldMap L G) (rankLearnerInputLaw L P)
      (mixedRankTableWorldLaw P G (rankLearnerTableLaw L G)) := by
  have hSeed : MeasurePreserving (rankLearnerStrategyTable L G) L.seedLaw (rankLearnerTableLaw L G) :=
    ⟨measurable_rankLearnerStrategyTable L G,rfl⟩
  exact (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
    ((MeasurePreserving.id (P.reservoirLaw k)).prod hSeed))

lemma rankLearnerInputLaw_grid_ae (L : RankLearner n k) (G : Finset ℝ) (P : Instance n)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) :
    ∀ᵐ ω ∂rankLearnerInputLaw L P, (∀ i, ω.1 i∈G) ∧ ∀ i j, ω.2.2.1 i j∈G := by
  have hX : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i∈G := ae_all_iff.mpr fun i =>
    (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hG i)
  have hY : ∀ᵐ y ∂P.reservoirLaw k, ∀ i j, y i j∈G := ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    (P.reservoir_coordinate_measurePreserving k i j).quasiMeasurePreserving.ae (hG i)
  have hpX : MeasurePreserving (fun ω : RankLearnerInputWorld L => ω.1) (rankLearnerInputLaw L P) P.valuesLaw :=
    measurePreserving_fst
  have h0 := measurePreserving_fst (μ := P.reservoirLaw k) (ν := L.seedLaw)
  have h1 := measurePreserving_snd (μ := Instance.uniformPermutationLaw n) (ν := (P.reservoirLaw k).prod L.seedLaw)
  have h2 := measurePreserving_snd (μ := P.valuesLaw)
    (ν := (Instance.uniformPermutationLaw n).prod ((P.reservoirLaw k).prod L.seedLaw))
  have hpY : MeasurePreserving (fun ω : RankLearnerInputWorld L => ω.2.2.1) (rankLearnerInputLaw L P) (P.reservoirLaw k) :=
    h0.comp (h1.comp h2)
  exact (hpX.quasiMeasurePreserving.ae hX).and (hpY.quasiMeasurePreserving.ae hY)

lemma rankLearnerTableMixture_expectedReward (L : RankLearner n k) (G : Finset ℝ)
    (hCap : ∀ y r q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ y r q i H, L.policy.decide (y,r) q i 0 H = false)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) :
    (rankLearnerTableMixture L G).expectedReward P = L.expectedReward P := by
  let f := fun ω : MixedRankTableWorld n k G =>
    (rankLearnerTableMixture L G).policy.reward ω.2.2 ω.2.1 ω.1
  have hI : Integrable f (mixedRankTableWorldLaw P G (rankLearnerTableLaw L G)) :=
    ((rankLearnerTableMixture L G).randomizedPolicy P).integrable_realizedReward P hP
  have hp := rankLearnerTableWorldMap_measurePreserving L G P
  have hMean := hp.hasLaw.integral_comp hI.aestronglyMeasurable
  have hEq : (fun ω => f (rankLearnerTableWorldMap L G ω)) =ᵐ[rankLearnerInputLaw L P]
      (fun ω => L.policy.reward ω.2.2 ω.2.1 ω.1) := by
    filter_upwards [rankLearnerInputLaw_grid_ae L G P hG] with ω hω
    exact (mixedRankTableLearner_reward G (rankLearnerTableLaw L G) ω.2.2.1
      (rankLearnerStrategyTable L G ω.2.2.2) ω.2.1 ω.1).trans
      (finiteRankTablePolicy_reward L G ω.2.2.2 ω.2.2.1 ω.1 hω.2 hω.1
        (hCap ω.2.2.1 ω.2.2.2) (hZero ω.2.2.1 ω.2.2.2) ω.2.1)
  exact hMean.symm.trans (integral_congr_ae hEq)

lemma rankLearnerTableMixture_reachProbability (L : RankLearner n k) (G : Finset ℝ)
    (hCap : ∀ y r q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ y r q i H, L.policy.decide (y,r) q i 0 H = false)
    (P : Instance n) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (i : Fin n) :
    (rankLearnerTableMixture L G).reachProbability P i = L.reachProbability P i := by
  let E : Set (MixedRankTableWorld n k G) :=
    {ω | (rankLearnerTableMixture L G).policy.Reaches ω.2.2 ω.2.1 ω.1 i}
  have hE : MeasurableSet E :=
    (rankLearnerTableMixture L G).policy.measurableSet_reaches (rankLearnerTableMixture L G).policy_isMeasurable
      (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst) i
  have hp := rankLearnerTableWorldMap_measurePreserving L G P
  have hEq : rankLearnerTableWorldMap L G ⁻¹' E =ᵐ[rankLearnerInputLaw L P]
      {ω | L.policy.Reaches ω.2.2 ω.2.1 ω.1 i} := by
    filter_upwards [rankLearnerInputLaw_grid_ae L G P hG] with ω hω
    apply propext
    exact (mixedRankTableLearner_reaches G (rankLearnerTableLaw L G) ω.2.2.1
      (rankLearnerStrategyTable L G ω.2.2.2) ω.2.1 ω.1 i).trans
      (finiteRankTablePolicy_reaches L G ω.2.2.2 ω.2.2.1 ω.1 hω.2 hω.1
        (hCap ω.2.2.1 ω.2.2.2) (hZero ω.2.2.1 ω.2.2.2) ω.2.1 i)
  exact (congrArg ENNReal.toReal (hp.measure_preimage hE.nullMeasurableSet)).symm.trans
    (congrArg ENNReal.toReal (measure_congr hEq))

end ProphetSecretary.Statistics
