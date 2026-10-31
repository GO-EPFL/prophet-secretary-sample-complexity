import ProphetSecretary.Limiting.IgnorePoisson

/-!
# Zero-intensity boundary of the hybrid model

Zero intensity produces the empty actual configuration almost surely. A shared
hybrid policy then induces an ordinary finite policy by supplying empty anonymous
history. This proves the scalar-value boundary against all competing policies.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

noncomputable def emptyConfiguration : Configuration := configurationMk 0 (fun j => Fin.elim0 j)

lemma configurationLaw_zero : configurationLaw (0 : FiniteMeasure ℝ) = Measure.dirac emptyConfiguration := by
  have hz : ∀ᵐ ω : Configuration ∂configurationLaw (0 : FiniteMeasure ℝ), (ω.1 : ℝ) = 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun ω : Configuration => Nat.cast_nonneg ω.1)
      (configuration_count_integrable 0)).mp
    simpa using configuration_count_expectation (0 : FiniteMeasure ℝ)
  have he : (id : Configuration → Configuration) =ᵐ[configurationLaw (0 : FiniteMeasure ℝ)]
      (fun _ => emptyConfiguration) := by
    filter_upwards [hz] with ω hω
    rcases ω with ⟨N, pts⟩
    have hN : N = 0 := by exact_mod_cast hω
    subst N
    change configurationMk 0 pts = configurationMk 0 (fun j => Fin.elim0 j)
    congr 1
    funext j
    exact Fin.elim0 j
  calc
    _ = (configurationLaw (0 : FiniteMeasure ℝ)).map id := by rw [Measure.map_id]
    _ = (configurationLaw (0 : FiniteMeasure ℝ)).map (fun _ => emptyConfiguration) := Measure.map_congr he
    _ = _ := by rw [Measure.map_const, measure_univ, one_smul]

lemma zeroIntensityWorld_measurePreserving {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Model.Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : Model.World n Seed => (emptyConfiguration, v))
      (P.worldLaw ν) (hybridWorldLaw P 0 ν) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hybridWorldLaw, worldLaw, configurationLaw_zero, Measure.dirac_prod]

variable {n : ℕ}

noncomputable def emptyPoissonPolicy (π : RandomizedHybridPolicy n) : Model.RandomizedPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := ⟨fun r t i x H => π.rule.individual r t i x H 0⟩
  measurable_rule := by
    exact π.measurable_rule.1.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
          ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk measurable_const)))))

lemma emptyPoissonPolicy_adapter (π : RandomizedHybridPolicy n) :
    π.rule.asFinitePolicy 0 = (emptyPoissonPolicy π).rule := by
  change Model.Policy.mk _ = Model.Policy.mk _
  congr 1
  funext r t i x H
  have hH : retainedHistory (N := 0) H = H := by funext j; rfl
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.addCases_left]
    simp [hH, poissonHistory]
  | right j => exact Fin.elim0 j

lemma emptyPoissonPolicy_outcomes (π : RandomizedHybridPolicy n) (v : Model.World n π.Seed) :
    π.rule.realizedDuration (emptyConfiguration, v) = (emptyPoissonPolicy π).realizedDuration v ∧
      π.rule.realizedReward 0 (emptyConfiguration, v) = (emptyPoissonPolicy π).realizedReward v := by
  have hx : combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) = v.1 := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [combinedValues, Fin.addCases_left]
      congr 1
    | right j => exact Fin.elim0 j
  have hu : combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) = v.2.1 := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [combinedClocks, Fin.addCases_left]
      congr 1
    | right j => exact Fin.elim0 j
  constructor
  · change (π.rule.asFinitePolicy 0).stoppingTime v.2.2 Finset.univ _ _ = _
    erw [emptyPoissonPolicy_adapter, hx, hu]
    rfl
  · have hb := π.finiteEvaluation_reward 0 ((fun j : Fin 0 => (Fin.elim0 j : Point)), v)
    dsimp only at hb
    rw [hx, hu] at hb
    change π.rule.realizedReward 0 (emptyConfiguration, v) = _
    erw [← hb]
    change (π.rule.asFinitePolicy 0).reward v.2.2 Finset.univ v.1 v.2.1 = _
    erw [emptyPoissonPolicy_adapter]
    rfl

lemma emptyPoissonPolicy_scalarObjective (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity = 0) (w c : ℝ) :
    π.scalarObjective B w c = (emptyPoissonPolicy π).scalarObjective B.individuals w c := by
  have hmp := zeroIntensityWorld_measurePreserving B.individuals π.seedLaw
  have hm : Measurable (fun v : HybridWorld n π.Seed =>
      w * π.rule.realizedReward 0 v + c * π.rule.realizedDuration v) :=
    ((π.rule.measurable_realizedReward π.measurable_rule 0).const_mul w).add
      ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have h := integral_map (μ := B.individuals.worldLaw π.seedLaw) hmp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmp.map_eq] at h
  unfold RandomizedHybridPolicy.scalarObjective
  rw [ha]
  change (∫ v, w * π.rule.realizedReward 0 v + c * π.rule.realizedDuration v ∂hybridWorldLaw B.individuals B.intensity π.seedLaw) = _
  rw [hμ, h]
  unfold Model.RandomizedPolicy.scalarObjective
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    dsimp only
    erw [(emptyPoissonPolicy_outcomes π v).1, (emptyPoissonPolicy_outcomes π v).2])

lemma FiniteIntensityHybridInstance.value_zero_intensity (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity = 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = Model.optimalScalarValue B.individuals w c := by
  apply le_antisymm
  · apply csSup_le (B.scalarPayoffs_nonempty w c)
    rintro _ ⟨π, rfl⟩
    dsimp only
    rw [emptyPoissonPolicy_scalarObjective π B ha hμ w c]
    exact Model.scalarObjective_le_optimal _ B.individuals
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hw hc
  · exact B.finiteValue_le ha w c

end ProphetSecretary.Limiting
