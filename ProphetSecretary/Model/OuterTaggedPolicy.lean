import ProphetSecretary.Model.OuterRetentionMean
import ProphetSecretary.Model.ValueTransform
import ProphetSecretary.Reach.FiniteReach
import ProphetSecretary.Probability.ProductRegrouping

/-!
# A policy acting on tagged retained observations

The auxiliary tag vector is used only to transform the current and present past
values. The underlying policy receives its original seed. The actual product
world maps to the retained instance with independent arrival clocks and seed.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def RandomizedPolicy.taggedRetainedPullback (π : RandomizedPolicy n) (t : ℝ × ℝ) : RandomizedPolicy n where
  Seed := (Fin n → ℝ) × π.Seed
  seedLaw := (Instance.clocksLaw n).prod π.seedLaw
  rule := π.rule.pullbackValuesBy Prod.snd (fun (r : (Fin n → ℝ) × π.Seed) i x => retainAboveTag t (x,r.1 i))
  measurable_rule := π.rule.pullbackValuesBy_isMeasurable π.measurable_rule Prod.snd measurable_snd
    (fun (r : (Fin n → ℝ) × π.Seed) i x => retainAboveTag t (x,r.1 i)) (fun i =>
      measurable_retainAboveTag.comp (measurable_const.prodMk
        (measurable_snd.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)))))

noncomputable def taggedRetainedWorld {Seed : Type*} (t : ℝ × ℝ) (ω : World n ((Fin n → ℝ) × Seed)) : World n Seed :=
  (fun i => retainAboveTag t (ω.1 i,ω.2.2.1 i),(ω.2.1,ω.2.2.2))

lemma Instance.taggedRetainedWorld_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (t : ℝ × ℝ) :
    MeasurePreserving (taggedRetainedWorld (n:=n) (Seed:=Seed) t)
      (P.worldLaw ((Instance.clocksLaw n).prod ν)) ((P.retainedAtTag t).worldLaw ν) := by
  have hPairs : MeasurePreserving (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => (p.1 i,p.2 i))
      (P.valuesLaw.prod (Instance.clocksLaw n)) P.taggedValuesLaw :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) P.law (fun _ => Instance.uniformClock)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  have hValues := (P.taggedRetainedValues_measurePreserving t).comp hPairs
  have h0 := (measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) ((Instance.clocksLaw n).prod ν)).symm
    (MeasurableEquiv.prodAssoc : (((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × Seed)) ≃ᵐ
      ((Fin n → ℝ) × ((Fin n → ℝ) × ((Fin n → ℝ) × Seed))))
  have h1 := ProphetSecretary.Probability.productPairShuffle_measurePreserving P.valuesLaw (Instance.clocksLaw n) (Instance.clocksLaw n) ν
  exact (hValues.prod (MeasurePreserving.id ((Instance.clocksLaw n).prod ν))).comp (h1.comp h0)

lemma Policy.reward_pullbackValuesBy_ge {Seed NewSeed : Type*} (π : Policy Seed n)
    (s : NewSeed → Seed) (g : NewSeed → Fin n → ℝ → ℝ)
    (r : NewSeed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (hDown : ∀ i, g r i (x i)≤x i) :
    π.reward (s r) D (fun i => g r i (x i)) u≤(π.pullbackValuesBy s g).reward r D x u := by
  unfold Policy.reward
  apply Finset.sum_le_sum
  intro i _
  have hSel := π.pullbackValuesBy_actualSelects_iff s g r D x u i
  by_cases hi : (π.pullbackValuesBy s g).ActualSelects r D x u i
  · simp only [if_pos hi,if_pos (hSel.mp hi)]
    exact hDown i
  · simp only [if_neg hi,if_neg (fun h => hi (hSel.mpr h)),le_refl]

/-- Acting on retained displays while collecting original offers can only increase reward. -/
theorem RandomizedPolicy.taggedRetainedPullback_expectedReward_ge (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (t : ℝ × ℝ) :
    π.expectedReward (P.retainedAtTag t)≤(π.taggedRetainedPullback t).expectedReward P := by
  have hMP := P.taggedRetainedWorld_measurePreserving π.seedLaw t
  have hMap := integral_map (μ:=P.worldLaw ((Instance.clocksLaw n).prod π.seedLaw)) hMP.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  have hLeft := hMP.integrable_comp_of_integrable (π.integrable_realizedReward (P.retainedAtTag t) (P.retainedAtTag_integrable_maximum hP t))
  have hRight := (π.taggedRetainedPullback t).integrable_realizedReward P hP
  change (∫ ω, π.realizedReward ω ∂(P.retainedAtTag t).worldLaw π.seedLaw)≤_
  rw [hMap]
  change (∫ ω, π.realizedReward (taggedRetainedWorld t ω) ∂P.worldLaw ((Instance.clocksLaw n).prod π.seedLaw))≤
    ∫ ω, (π.taggedRetainedPullback t).realizedReward ω ∂P.worldLaw ((Instance.clocksLaw n).prod π.seedLaw)
  apply integral_mono_ae hLeft hRight
  have hX := (measurePreserving_fst (μ:=P.valuesLaw) (ν:=(Instance.clocksLaw n).prod ((Instance.clocksLaw n).prod π.seedLaw))).quasiMeasurePreserving.ae P.ae_nonnegative
  filter_upwards [hX] with ω hω
  apply π.rule.reward_pullbackValuesBy_ge Prod.snd (fun (r : (Fin n → ℝ) × π.Seed) i x => retainAboveTag t (x,r.1 i)) ω.2.2 Finset.univ ω.1 ω.2.1
  intro i
  exact retainAboveTag_le_value t (ω.1 i,ω.2.2.1 i) (hω i)

lemma RandomizedPolicy.taggedRetainedPullback_reachProbability (π : RandomizedPolicy n) (P : Instance n)
    (t : ℝ × ℝ) (i : Fin n) :
    (π.taggedRetainedPullback t).rule.reachProbability P (π.taggedRetainedPullback t).seedLaw i=
      π.rule.reachProbability (P.retainedAtTag t) π.seedLaw i := by
  have hMP := P.taggedRetainedWorld_measurePreserving π.seedLaw t
  let E : Set (ProphetSecretary.Model.World n π.Seed) := {ω | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i}
  have hE : MeasurableSet E := π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  unfold Policy.reachProbability
  rw [←hMP.map_eq,map_measureReal_apply hMP.measurable hE]
  congr 1
  ext ω
  change ω.2.1 i≤(π.rule.pullbackValuesBy Prod.snd
      (fun (r : (Fin n → ℝ) × π.Seed) j x => retainAboveTag t (x,r.1 j))).stoppingTime
        ω.2.2 Finset.univ ω.1 ω.2.1 ↔
    ω.2.1 i≤π.rule.stoppingTime ω.2.2.2 Finset.univ (fun j => retainAboveTag t (ω.1 j,ω.2.2.1 j)) ω.2.1
  rw [Policy.pullbackValuesBy_stoppingTime]

end ProphetSecretary.Model
