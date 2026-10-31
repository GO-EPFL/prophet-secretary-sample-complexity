import ProphetSecretary.Limiting.HybridBranchLaw
import ProphetSecretary.Model.Simulation

/-!
# Ignoring anonymous arrivals

Every admissible finite-instance policy is also a hybrid policy. Its decisions
ignore the anonymous past and reject every anonymous candidate. Duration is
unchanged, and with terminal reward zero the selected reward is unchanged on
every path, including tied clocks.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def ignorePoisson (π : Model.RandomizedPolicy n) : RandomizedHybridPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := ⟨fun r t i x H _ => π.rule.decide r t i x H, fun _ _ _ _ _ => false⟩
  measurable_rule := by
    constructor
    · let Ω := π.Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
      have hp : Measurable (fun z : Ω => (z.1, (z.2.1, (z.2.2.1, (z.2.2.2.1, z.2.2.2.2.1))))) := by fun_prop
      exact π.measurable_rule.comp hp
    · exact measurable_const

lemma ignorePoisson_adapter (π : Model.RandomizedPolicy n) (N : ℕ) :
    (ignorePoisson π).rule.asFinitePolicy N = π.rule.ignoreExtras (Fin.castAddEmb N) := by
  change Model.Policy.mk _ = Model.Policy.mk _
  congr 1
  funext r t i x H
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.addCases_left, ignorePoisson]
    have hH : retainedHistory H = Model.projectHistory (Fin.castAddEmb N) H := rfl
    simp only [Fin.castAddEmb_apply, Fin.castAdd_inj, exists_eq_left, hH]
    cases π.rule.decide r t i x (Model.projectHistory (Fin.castAddEmb N) H) <;> rfl
  | right j =>
    have hne (i : Fin n) : Fin.castAdd N i ≠ Fin.natAdd n j := by
      intro hij
      have hv := congrArg Fin.val hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp [ignorePoisson, hne]

lemma ignorePoisson_duration (π : Model.RandomizedPolicy n) (v : HybridWorld n π.Seed) :
    (ignorePoisson π).rule.realizedDuration v = π.realizedDuration v.2 := by
  change ((ignorePoisson π).rule.asFinitePolicy v.1.1).stoppingTime v.2.2.2 Finset.univ
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) = _
  erw [ignorePoisson_adapter, Model.Policy.ignoreExtras_stoppingTime]
  have hx : combinedValues v.2.1 v.1.2 ∘ Fin.castAddEmb v.1.1 = v.2.1 := by
    funext i
    simp [combinedValues]
  have hu : combinedClocks v.2.2.1 v.1.2 ∘ Fin.castAddEmb v.1.1 = v.2.2.1 := by
    funext i
    simp [combinedClocks]
  rw [hx, hu]
  rfl

lemma ignorePoisson_reward_zero (π : Model.RandomizedPolicy n) (v : HybridWorld n π.Seed) :
    (ignorePoisson π).rule.realizedReward 0 v = π.realizedReward v.2 := by
  have hb := (ignorePoisson π).finiteEvaluation_reward v.1.1 (v.1.2, v.2)
  have hb' : (ignorePoisson π).rule.realizedReward 0 v =
      ((ignorePoisson π).finiteEvaluation v.1.1).realizedReward
        (combinedValues v.2.1 v.1.2, (combinedClocks v.2.2.1 v.1.2, v.2.2.2)) := by
    have hv : (configurationMk v.1.1 v.1.2, v.2) = v := by
      rcases v with ⟨⟨N, pts⟩, b⟩
      rfl
    dsimp only at hb
    erw [hv] at hb
    exact hb.symm
  erw [hb']
  change ((ignorePoisson π).rule.asFinitePolicy v.1.1).reward v.2.2.2 Finset.univ
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) = _
  erw [ignorePoisson_adapter]
  let e : Fin n ↪o Fin (n + v.1.1) := ⟨Fin.castAddEmb v.1.1, by intro a b; rfl⟩
  erw [π.rule.ignoreExtras_reward_orderEmbedding e]
  have hx : combinedValues v.2.1 v.1.2 ∘ e = v.2.1 := by funext i; simp [combinedValues, e]
  have hu : combinedClocks v.2.2.1 v.1.2 ∘ e = v.2.2.1 := by funext i; simp [combinedClocks, e]
  rw [hx, hu]
  rfl

lemma ignorePoisson_scalarObjective (π : Model.RandomizedPolicy n) (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (w c : ℝ) :
    (ignorePoisson π).scalarObjective B w c = π.scalarObjective B.individuals w c := by
  have hmp := measurePreserving_snd (μ := configurationLaw B.intensity) (ν := B.individuals.worldLaw π.seedLaw)
  change MeasurePreserving Prod.snd (B.law π.seedLaw) (B.individuals.worldLaw π.seedLaw) at hmp
  have hm : Measurable (fun ω : π.World => w * π.realizedReward ω + c * π.realizedDuration ω) :=
    (π.measurable_realizedReward.const_mul w).add (π.measurable_realizedDuration.const_mul c)
  have h := integral_map (μ := B.law π.seedLaw) hmp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmp.map_eq] at h
  unfold RandomizedHybridPolicy.scalarObjective Model.RandomizedPolicy.scalarObjective
  rw [ha]
  simp only [NNReal.coe_zero]
  calc
    _ = ∫ v, w * π.realizedReward v.2 + c * π.realizedDuration v.2 ∂B.law π.seedLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by
        dsimp only
        erw [ignorePoisson_reward_zero, ignorePoisson_duration])
    _ = _ := h.symm

lemma FiniteIntensityHybridInstance.finiteValue_le (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (w c : ℝ) :
    Model.optimalScalarValue B.individuals w c ≤ B.optimalScalarValue w c := by
  apply csSup_le (Model.scalarValues_nonempty B.individuals w c)
  rintro v ⟨π, rfl⟩
  rw [← ignorePoisson_scalarObjective π B ha w c]
  exact B.scalarObjective_le_value _ w c

end ProphetSecretary.Limiting
