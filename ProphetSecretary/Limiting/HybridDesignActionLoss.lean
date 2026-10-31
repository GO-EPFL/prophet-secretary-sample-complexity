import ProphetSecretary.Limiting.HybridGeneratorVerification
import ProphetSecretary.Limiting.HybridClockNullSets

/-!
# Reached finite-design action loss in the actual hybrid model

The finite potential Q supplies continuation values; the executed hybrid
policy is arbitrary. Each anonymous configuration branch uses Q with matching
deterministic-zero comparison identities, while every actual offer and its
history remain present. Measurability and integrability are proved before
mixing the analytical count branches.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

noncomputable def HybridRule.designActionLoss (π : HybridRule n Seed) (Q : Model.Instance n)
    (w c : ℝ) (v : HybridWorld n Seed) : ℝ :=
  (π.asFinitePolicy v.1.1).reachedBellmanLoss (Q.appendZeros v.1.1) w c v.2.2.2
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)

lemma HybridRule.designActionLoss_nonnegative (π : HybridRule n Seed) (Q : Model.Instance n)
    (w c : ℝ) (v : HybridWorld n Seed) : 0 ≤ π.designActionLoss Q w c v :=
  (π.asFinitePolicy v.1.1).reachedBellmanLoss_nonnegative (Q.appendZeros v.1.1) w c _ _ _

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_designActionLoss (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : Measurable (π.designActionLoss Q w c) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := by fun_prop
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact (π.asFinitePolicy N).measurable_reachedBellmanLoss (π.asFinitePolicy_isMeasurable hπ N)
    (Q.appendZeros N) (Q.appendZeros_integrable_maximum N hQ) hw hc hr
    (fun k => measurable_combinedValues_family _ hx _ hv k)
    (fun k => measurable_combinedClocks_family _ hu _ hv k)

lemma HybridRule.integrable_designActionLoss (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : Integrable (π.designActionLoss Q w c) (B.law ν) := by
  have hCount : Integrable (fun v : HybridWorld n Seed => (v.1.1 : ℝ)) (B.law ν) :=
    (measurePreserving_fst (μ := configurationLaw B.intensity) (ν := B.individuals.worldLaw ν)).integrable_comp_of_integrable
      (configuration_count_integrable B.intensity)
  let K := w*(B.cap : ℝ)+Model.optimalScalarValue Q w c
  have hDom : Integrable (fun v : HybridWorld n Seed => ((n : ℝ)+(v.1.1 : ℝ))*K) (B.law ν) :=
    ((integrable_const (n : ℝ)).add hCount).mul_const K
  apply hDom.mono' (π.measurable_designActionLoss hπ Q hQ hw hc).aestronglyMeasurable
  filter_upwards [realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported,
    hybrid_combined_clocks_regular B.individuals B.intensity ν] with v hx ht
  rw [Real.norm_eq_abs,abs_of_nonneg (π.designActionLoss_nonnegative Q w c v)]
  have h := (π.asFinitePolicy v.1.1).reachedBellmanLoss_le_sum (Q.appendZeros v.1.1)
    (Q.appendZeros_integrable_maximum v.1.1 hQ) hw.le hc v.2.2.2
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
    (fun i => (hx i).1) (fun i => (ht.2 i).1.le)
  rw [Q.optimalScalarValue_appendZeros v.1.1 hQ hw.le hc] at h
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin (n+v.1.1), K := Finset.sum_le_sum fun i _ =>
      add_le_add (mul_le_mul_of_nonneg_left (hx i).2 hw.le) le_rfl
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]

noncomputable def RandomizedHybridPolicy.expectedDesignActionLoss (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (B : FiniteIntensityHybridInstance n) (w c : ℝ) : ℝ :=
  ∫ v, π.rule.designActionLoss Q w c v ∂B.law π.seedLaw

lemma RandomizedHybridPolicy.expectedDesignActionLoss_nonnegative (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (B : FiniteIntensityHybridInstance n) (w c : ℝ) :
    0 ≤ π.expectedDesignActionLoss Q B w c := integral_nonneg (π.rule.designActionLoss_nonnegative Q w c)

lemma RandomizedHybridPolicy.designActionLoss_branchIntegral (π : RandomizedHybridPolicy n)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, π.rule.designActionLoss Q w c (configurationMk N v.1,v.2)
      ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw π.seedLaw)) =
      (π.finiteEvaluation N).expectedReachedDesignActionLoss (Q.appendZeros N) (appendIID P κ hκ N) w c := by
  have hm : Measurable (fun ω : (π.finiteEvaluation N).World =>
      (π.finiteEvaluation N).rule.reachedBellmanLoss (Q.appendZeros N) w c ω.2.2 ω.1 ω.2.1) :=
    (π.finiteEvaluation N).rule.measurable_reachedBellmanLoss (π.finiteEvaluation N).measurable_rule
      (Q.appendZeros N) (Q.appendZeros_integrable_maximum N hQ) hw hc
      (by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop)
  have hmp := finiteArrayWorld_measurePreserving P κ hκ π.seedLaw N
  have h := integral_map (μ := (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod
    (P.worldLaw π.seedLaw)) hmp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

end ProphetSecretary.Limiting
