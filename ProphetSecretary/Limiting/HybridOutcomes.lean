import ProphetSecretary.Limiting.HybridPolicy
import ProphetSecretary.Model.Outcome

/-!
# Hybrid selected reward and prophet maximum

An actual first selection receives that offer's value. If no offer is selected,
the fixed terminal reward is received at time one. The benchmark includes every
actual anonymous point and every retained individual, independently of stopping.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {n N : ℕ} {Seed : Type*}

def HybridRule.HasSelection (π : HybridRule n Seed) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) : Prop :=
  ∃ k : Fin (n + ω.1), (π.asFinitePolicy ω.1).ActualSelects r Finset.univ
    (combinedValues x ω.2) (combinedClocks u ω.2) k

noncomputable def HybridRule.reward (π : HybridRule n Seed) (a : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) : ℝ :=
  if π.HasSelection r x u ω then
    (π.asFinitePolicy ω.1).reward r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) else a

noncomputable def HybridRule.realizedReward (π : HybridRule n Seed) (a : ℝ) (v : HybridWorld n Seed) : ℝ :=
  π.reward a v.2.2.2 v.2.1 v.2.2.1 v.1

lemma HybridRule.measurable_reward_family {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (π : HybridRule n Seed) (hπ : π.IsMeasurable) (a : ℝ)
    (r : Ω → Seed) (hr : Measurable r) (x u : Ω → Fin n → ℝ)
    (hx : ∀ i, Measurable (fun ω => x ω i)) (hu : ∀ i, Measurable (fun ω => u ω i))
    (v : Ω → Fin N → Point) (hv : ∀ j, Measurable (fun ω => v ω j)) :
    Measurable (fun ω => π.reward a (r ω) (x ω) (u ω) (configurationMk N (v ω))) := by
  have hX (k : Fin (n + N)) := measurable_combinedValues_family x hx v hv k
  have hU (k : Fin (n + N)) := measurable_combinedClocks_family u hu v hv k
  have hsel : MeasurableSet {ω : Ω | ∃ k : Fin (n + N), (π.asFinitePolicy N).ActualSelects (r ω) Finset.univ
      (combinedValues (x ω) (v ω)) (combinedClocks (u ω) (v ω)) k} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun k => (π.asFinitePolicy N).measurableSet_actualSelects
      (π.asFinitePolicy_isMeasurable hπ N) hr hX hU Finset.univ k)
  exact Measurable.ite hsel ((π.asFinitePolicy N).measurable_reward (π.asFinitePolicy_isMeasurable hπ N)
    hr hX hU Finset.univ) measurable_const

lemma HybridRule.measurable_realizedReward [MeasurableSpace Seed] (π : HybridRule n Seed)
    (hπ : π.IsMeasurable) (a : ℝ) : Measurable (π.realizedReward a) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × ProphetSecretary.Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact π.measurable_reward_family hπ a _ hr _ _ hx hu _ hv

lemma HybridRule.reward_eq_of_selection (π : HybridRule n Seed) (a : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (k : Fin (n + ω.1))
    (hk : (π.asFinitePolicy ω.1).ActualSelects r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k) :
    π.reward a r x u ω = combinedValues x ω.2 k := by
  rw [HybridRule.reward, if_pos (show π.HasSelection r x u ω from ⟨k, hk⟩)]
  exact (π.asFinitePolicy ω.1).reward_eq_of_actualSelects _ _ _ _ hk

lemma HybridRule.reward_eq_terminal_of_no_selection (π : HybridRule n Seed) (a : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (h : ¬π.HasSelection r x u ω) : π.reward a r x u ω = a := by
  rw [HybridRule.reward, if_neg h]

lemma HybridRule.reward_nonnegative (π : HybridRule n Seed) {a : ℝ} (ha : 0 ≤ a) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (hx : ∀ k, 0 ≤ combinedValues x ω.2 k) :
    0 ≤ π.reward a r x u ω := by
  unfold HybridRule.reward
  split_ifs
  · exact (π.asFinitePolicy ω.1).reward_nonnegative _ _ _ _ hx
  · exact ha

noncomputable def hybridMaximum (a : ℝ) (v : Configuration × (Fin n → ℝ)) : ℝ :=
  max a (ProphetSecretary.Model.Instance.maximum (combinedValues v.2 v.1.2))

lemma hybridMaximum_nonnegative (a : ℝ) (v : Configuration × (Fin n → ℝ)) : 0 ≤ hybridMaximum a v :=
  (ProphetSecretary.Model.Instance.maximum_nonnegative _).trans (le_max_right _ _)

lemma HybridRule.reward_le_maximum (π : HybridRule n Seed) (a : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) : π.reward a r x u ω ≤ hybridMaximum a (ω, x) := by
  unfold HybridRule.reward hybridMaximum
  split_ifs
  · exact ((π.asFinitePolicy ω.1).reward_le_maximum _ _ _ _).trans (le_max_right _ _)
  · exact le_max_left _ _

lemma measurable_hybridMaximum (a : ℝ) : Measurable (@hybridMaximum n a) := by
  apply measurable_of_configuration_prod_branches
  intro N
  have hx (i : Fin n) : Measurable (fun v : (Fin N → Point) × (Fin n → ℝ) => v.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hv (j : Fin N) : Measurable (fun v : (Fin N → Point) × (Fin n → ℝ) => v.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hX : Measurable (fun v : (Fin N → Point) × (Fin n → ℝ) => combinedValues v.2 v.1) :=
    measurable_pi_lambda _ (fun k => measurable_combinedValues_family _ hx _ hv k)
  exact measurable_const.max (ProphetSecretary.Model.Instance.measurable_maximum.comp hX)

noncomputable def hybridValueLaw (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) :
    Measure (Configuration × (Fin n → ℝ)) := (configurationLaw μ).prod P.valuesLaw

instance hybridValueLaw_isProbability (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) :
    IsProbabilityMeasure (hybridValueLaw P μ) := by
  unfold hybridValueLaw
  infer_instance

lemma hybridValue_projection_measurePreserving [MeasurableSpace Seed] (P : ProphetSecretary.Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : HybridWorld n Seed => (v.1, v.2.1)) (hybridWorldLaw P μ ν) (hybridValueLaw P μ) := by
  exact (MeasurePreserving.id (configurationLaw μ)).prod (measurePreserving_fst :
    MeasurePreserving (fun v : ProphetSecretary.Model.World n Seed => v.1) (P.worldLaw ν) P.valuesLaw)

noncomputable def hybridExpectedMaximum (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (a : ℝ) : ℝ :=
  ∫ v, hybridMaximum a v ∂hybridValueLaw P μ

lemma hybridValueLaw_values_bounds (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) {H : ℝ}
    (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    ∀ᵐ v ∂hybridValueLaw P μ, ∀ k : Fin (n + v.1.1),
      0 ≤ combinedValues v.2 v.1.2 k ∧ combinedValues v.2 v.1.2 k ≤ H := by
  have hp : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hP i))
  have hp' : ∀ᵐ x ∂P.valuesLaw, ∀ i, 0 ≤ x i ∧ x i ≤ H := by
    filter_upwards [P.ae_nonnegative, hp] with x hx hb
    exact fun i => ⟨hx i, hb i⟩
  have hi := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.valuesLaw)).ae hp'
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := P.valuesLaw)).ae
    (configuration_points_mem_band μ H hμ)
  filter_upwards [hi, hc] with v hv hvp
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedValues, Fin.addCases_left] using hv i
  · simpa only [combinedValues, Fin.addCases_right] using And.intro (hvp j).2.1.le (hvp j).2.2

lemma hybridMaximum_le {a H : ℝ} (hH : 0 ≤ H) (ha : a ≤ H) (v : Configuration × (Fin n → ℝ))
    (hv : ∀ k, combinedValues v.2 v.1.2 k ≤ H) : hybridMaximum a v ≤ H :=
  max_le ha (ProphetSecretary.Model.Instance.maximum_le _ hH hv)

lemma integrable_hybridMaximum (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) {a H : ℝ}
    (hH : 0 ≤ H) (ha : a ≤ H) (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    Integrable (hybridMaximum a) (hybridValueLaw P μ) := by
  apply Integrable.of_bound (measurable_hybridMaximum a).aestronglyMeasurable H
  filter_upwards [hybridValueLaw_values_bounds P μ hP hμ] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (hybridMaximum_nonnegative a v)]
  exact hybridMaximum_le hH ha v (fun k => (hv k).2)

lemma hybridExpectedMaximum_nonnegative (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (a : ℝ) :
    0 ≤ hybridExpectedMaximum P μ a := integral_nonneg (hybridMaximum_nonnegative a)

lemma hybridExpectedMaximum_le (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) {a H : ℝ}
    (hH : 0 ≤ H) (ha : a ≤ H) (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    hybridExpectedMaximum P μ a ≤ H := by
  have hi := integrable_hybridMaximum P μ hH ha hP hμ
  have hb : ∀ᵐ v ∂hybridValueLaw P μ, hybridMaximum a v ≤ H :=
    (hybridValueLaw_values_bounds P μ hP hμ).mono (fun v hv => hybridMaximum_le hH ha v (fun k => (hv k).2))
  have he := integral_mono_ae hi (integrable_const H) hb
  simpa only [hybridExpectedMaximum, integral_const, probReal_univ, one_smul] using he

lemma realized_values_bounds [MeasurableSpace Seed] (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {H : ℝ}
    (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    ∀ᵐ v : HybridWorld n Seed ∂hybridWorldLaw P μ ν, ∀ k : Fin (n + v.1.1),
      0 ≤ combinedValues v.2.1 v.1.2 k ∧ combinedValues v.2.1 v.1.2 k ≤ H :=
  (hybridValue_projection_measurePreserving P μ ν).quasiMeasurePreserving.ae (hybridValueLaw_values_bounds P μ hP hμ)

lemma HybridRule.integrable_realizedReward [MeasurableSpace Seed] (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {a H : ℝ} (ha0 : 0 ≤ a) (hH : 0 ≤ H) (haH : a ≤ H)
    (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    Integrable (π.realizedReward a) (hybridWorldLaw P μ ν) := by
  apply Integrable.of_bound (π.measurable_realizedReward hπ a).aestronglyMeasurable H
  filter_upwards [realized_values_bounds P μ ν hP hμ] with v hv
  have hn := π.reward_nonnegative ha0 v.2.2.2 v.2.1 v.2.2.1 v.1 (fun k => (hv k).1)
  change ‖π.reward a v.2.2.2 v.2.1 v.2.2.1 v.1‖ ≤ H
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact (π.reward_le_maximum a _ _ _ _).trans (hybridMaximum_le hH haH (v.1, v.2.1) (fun k => (hv k).2))

noncomputable def HybridRule.expectedReward [MeasurableSpace Seed] (π : HybridRule n Seed)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (a : ℝ) (ν : Measure Seed) : ℝ :=
  ∫ v, π.realizedReward a v ∂hybridWorldLaw P μ ν

lemma HybridRule.expectedReward_le_maximum [MeasurableSpace Seed] (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {a H : ℝ} (ha0 : 0 ≤ a) (hH : 0 ≤ H) (haH : a ≤ H)
    (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    π.expectedReward P μ a ν ≤ hybridExpectedMaximum P μ a := by
  have hi := π.integrable_realizedReward hπ P μ ν ha0 hH haH hP hμ
  have hm := (hybridValue_projection_measurePreserving P μ ν).integrable_comp_of_integrable
    (integrable_hybridMaximum P μ hH haH hP hμ)
  have hb := integral_mono hi hm (fun v : HybridWorld n Seed => π.reward_le_maximum a v.2.2.2 v.2.1 v.2.2.1 v.1)
  have he := integral_map (μ := hybridWorldLaw P μ ν) (hybridValue_projection_measurePreserving P μ ν).measurable.aemeasurable
    (measurable_hybridMaximum a).aestronglyMeasurable
  rw [(hybridValue_projection_measurePreserving P μ ν).map_eq] at he
  exact hb.trans_eq he.symm

lemma hybridExpectedMaximum_ge_terminal (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) {a H : ℝ}
    (hH : 0 ≤ H) (ha : a ≤ H) (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) : a ≤ hybridExpectedMaximum P μ a := by
  have he := integral_mono (integrable_const a) (integrable_hybridMaximum P μ hH ha hP hμ)
    (fun v : Configuration × (Fin n → ℝ) => le_max_left a (ProphetSecretary.Model.Instance.maximum (combinedValues v.2 v.1.2)))
  simpa only [hybridExpectedMaximum, integral_const, probReal_univ, one_smul] using he

lemma HybridRule.expectedReward_nonnegative [MeasurableSpace Seed] (π : HybridRule n Seed)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {a H : ℝ} (ha : 0 ≤ a) (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) : 0 ≤ π.expectedReward P μ a ν := by
  apply integral_nonneg_of_ae
  filter_upwards [realized_values_bounds P μ ν hP hμ] with v hv
  exact π.reward_nonnegative ha _ _ _ _ (fun k => (hv k).1)

lemma HybridRule.expectedReward_le_cap [MeasurableSpace Seed] (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {a H : ℝ} (ha0 : 0 ≤ a) (hH : 0 ≤ H) (haH : a ≤ H)
    (hP : ∀ i, ∀ᵐ x : ℝ ∂P.law i, x ≤ H)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) : π.expectedReward P μ a ν ≤ H :=
  (π.expectedReward_le_maximum hπ P μ ν ha0 hH haH hP hμ).trans (hybridExpectedMaximum_le P μ hH haH hP hμ)

end ProphetSecretary.Limiting
