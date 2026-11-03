import ProphetSecretary.Probability.UniformMixtureIntegral
import ProphetSecretary.Model.ExecutionAgreement
import ProphetSecretary.Model.LearnerReachConditioning
import Mathlib.Probability.HasLaw

/-!
# One independent coin selects a complete online policy

With the mixing fraction fixed, an independent uniform coin chooses between
two causal rules sharing a query-seed space. Reward, duration and reach are
affine in that fraction under the actual product seed law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n : ℕ} {Seed : Type}

noncomputable def Policy.uniformMix (π σ : Policy Seed n) (α : ℝ) : Policy (Seed × ℝ) n where
  decide p t i x H := if p.2<α then σ.decide p.1 t i x H else π.decide p.1 t i x H

lemma Policy.uniformMix_isMeasurable [MeasurableSpace Seed] (π σ : Policy Seed n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable) (α : ℝ) : (π.uniformMix σ α).IsMeasurable := by
  let Ω := (Seed × ℝ) × (ℝ × (Fin n × (ℝ × History n)))
  have hInput : Measurable (fun p : Ω => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hCoin : MeasurableSet {p : Ω | p.1.2<α} :=
    measurableSet_lt (measurable_snd.comp measurable_fst) measurable_const
  exact Measurable.ite hCoin (hσ.comp hInput) (hπ.comp hInput)

lemma Policy.uniformMix_outcomes (π σ : Policy Seed n) (α : ℝ) (r : Seed) (c : ℝ)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.uniformMix σ α).reward (r,c) D x u = (if c<α then σ.reward r D x u else π.reward r D x u) ∧
    (π.uniformMix σ α).stoppingTime (r,c) D x u =
      (if c<α then σ.stoppingTime r D x u else π.stoppingTime r D x u) := by
  by_cases hc : c<α
  · simpa only [if_pos hc] using Policy.outcomes_eq_of_actions_eq (π.uniformMix σ α) σ (r,c) r D x u
      (fun i => by simp only [Policy.action,Policy.uniformMix,if_pos hc])
  · simpa only [if_neg hc] using Policy.outcomes_eq_of_actions_eq (π.uniformMix σ α) π (r,c) r D x u
      (fun i => by simp only [Policy.action,Policy.uniformMix,if_neg hc])

def uniformMixWorld (ω : World n (Seed × ℝ)) : World n Seed × ℝ :=
  ((ω.1,(ω.2.1,ω.2.2.1)),ω.2.2.2)

lemma uniformMixWorld_measurePreserving [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (uniformMixWorld (n := n) (Seed := Seed))
      (P.worldLaw (ν.prod Instance.uniformClock)) ((P.worldLaw ν).prod Instance.uniformClock) := by
  have h1 := (MeasurePreserving.id P.valuesLaw).prod
    ((measurePreserving_prodAssoc (Instance.clocksLaw n) ν Instance.uniformClock).symm MeasurableEquiv.prodAssoc)
  have h2 := (measurePreserving_prodAssoc P.valuesLaw ((Instance.clocksLaw n).prod ν)
    Instance.uniformClock).symm MeasurableEquiv.prodAssoc
  exact h2.comp h1

private lemma integral_uniformMixWorld_choice [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {f g : World n Seed → ℝ} (hf : Integrable f (P.worldLaw ν)) (hg : Integrable g (P.worldLaw ν))
    {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    (∫ ω : World n (Seed × ℝ), if ω.2.2.2<α then g (uniformMixWorld ω).1 else f (uniformMixWorld ω).1
      ∂P.worldLaw (ν.prod Instance.uniformClock)) =
      (1-α)*(∫ ω, f ω ∂P.worldLaw ν)+α*(∫ ω, g ω ∂P.worldLaw ν) := by
  have hI := integrable_uniform_coin_choice (P.worldLaw ν) hf hg α
  have hMap := (uniformMixWorld_measurePreserving P ν).hasLaw.integral_comp hI.aestronglyMeasurable
  exact hMap.trans (integral_uniform_coin_choice (P.worldLaw ν) hf hg hα)

lemma Policy.uniformMix_meanDuration [MeasurableSpace Seed] (π σ : Policy Seed n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable) (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    (π.uniformMix σ α).meanDuration P (ν.prod Instance.uniformClock) =
      (1-α)*π.meanDuration P ν+α*σ.meanDuration P ν := by
  unfold Policy.meanDuration
  calc
    _ = ∫ ω : World n (Seed × ℝ),
        if ω.2.2.2<α then σ.stoppingTime ω.2.2.1 Finset.univ ω.1 ω.2.1
        else π.stoppingTime ω.2.2.1 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (ν.prod Instance.uniformClock) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (π.uniformMix_outcomes σ α ω.2.2.1 ω.2.2.2 Finset.univ ω.1 ω.2.1).2)
    _ = _ := integral_uniformMixWorld_choice P ν
      (P.integrable_worldTime ν π hπ Finset.univ) (P.integrable_worldTime ν σ hσ Finset.univ) hα

/-- Realize a measurable rule under its specified independent seed law. -/
noncomputable def RandomizedPolicy.ofRule [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy Seed n) (hπ : π.IsMeasurable) : RandomizedPolicy n where
  Seed := Seed
  seedLaw := ν
  rule := π
  measurable_rule := hπ

lemma Policy.uniformMix_expectedReward [MeasurableSpace Seed] (π σ : Policy Seed n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    (RandomizedPolicy.ofRule (ν.prod Instance.uniformClock) (π.uniformMix σ α)
      (π.uniformMix_isMeasurable σ hπ hσ α)).expectedReward P =
      (1-α)*(RandomizedPolicy.ofRule ν π hπ).expectedReward P+
        α*(RandomizedPolicy.ofRule ν σ hσ).expectedReward P := by
  let πr := RandomizedPolicy.ofRule ν π hπ
  let σr := RandomizedPolicy.ofRule ν σ hσ
  calc
    _ = ∫ ω : World n (Seed × ℝ),
        if ω.2.2.2<α then σr.realizedReward (uniformMixWorld ω).1
        else πr.realizedReward (uniformMixWorld ω).1 ∂P.worldLaw (ν.prod Instance.uniformClock) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (π.uniformMix_outcomes σ α ω.2.2.1 ω.2.2.2 Finset.univ ω.1 ω.2.1).1)
    _ = _ := integral_uniformMixWorld_choice P ν (πr.integrable_realizedReward P hP)
      (σr.integrable_realizedReward P hP) hα

lemma Policy.uniformMix_reachProbability [MeasurableSpace Seed] (π σ : Policy Seed n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable) (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (i : Fin n) :
    (π.uniformMix σ α).reachProbability P (ν.prod Instance.uniformClock) i =
      (1-α)*π.reachProbability P ν i+α*σ.reachProbability P ν i := by
  rw [(π.uniformMix σ α).reachProbability_eq_integral_indicator (π.uniformMix_isMeasurable σ hπ hσ α),
    π.reachProbability_eq_integral_indicator hπ,σ.reachProbability_eq_integral_indicator hσ]
  have hI (p : Policy Seed n) (hp : p.IsMeasurable) :
      Integrable (fun ω : World n Seed => p.reachIndicator ω.2.2 ω.1 ω.2.1 i) (P.worldLaw ν) := by
    have hM := p.measurable_reachIndicator hp (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
    apply Integrable.of_bound hM.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      have h := p.reachIndicator_mem_unit ω.2.2 ω.1 ω.2.1 i
      change ‖p.reachIndicator ω.2.2 ω.1 ω.2.1 i‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg h.1]
      exact h.2
  calc
    _ = ∫ ω : World n (Seed × ℝ),
        if ω.2.2.2<α then σ.reachIndicator ω.2.2.1 ω.1 ω.2.1 i
        else π.reachIndicator ω.2.2.1 ω.1 ω.2.1 i ∂P.worldLaw (ν.prod Instance.uniformClock) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        have hTime := (π.uniformMix_outcomes σ α ω.2.2.1 ω.2.2.2 Finset.univ ω.1 ω.2.1).2
        simp only [Policy.reachIndicator,Policy.Reaches,hTime]
        split_ifs <;> rfl
    _ = _ := integral_uniformMixWorld_choice P ν (hI π hπ) (hI σ hσ) hα

end ProphetSecretary.Model
