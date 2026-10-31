import ProphetSecretary.Model.ConstantThreshold
import Mathlib.Probability.Independence.Integration

/-!
# The classical half-prophet bound within the finite random-arrival model

The proof uses one constant acceptance threshold. It optimizes neither arrival order
nor an instance-dependent stopping recursion.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma constantThresholdRule_reaches_of_no_qualifier (t : ℝ) (x u : Fin n → ℝ)
    (h : ∀ j, x j < t) (i : Fin n) (hi : u i ≤ 1) :
    (constantThresholdRule t n).Reaches () x u i := by
  apply ((constantThresholdRule t n).le_stoppingTime_iff () Finset.univ x u (u i)).mpr
  refine ⟨hi, ?_⟩
  intro j hj
  have ha := ((constantThresholdRule t n).mem_accepted _ _ _ _ j |>.mp hj).2
  exact False.elim ((not_le.mpr (h j)) ((constantThresholdRule_action _ _ _ _ _).mp ha))

/-- The expected positive-part tail of each offer. -/
noncomputable def Instance.excessMean (P : Instance n) (t : ℝ) (i : Fin n) : ℝ :=
  ∫ x, max (x - t) 0 ∂P.law i

lemma Instance.excessMean_nonnegative (P : Instance n) (t : ℝ) (i : Fin n) :
    0 ≤ P.excessMean t i := integral_nonneg fun _ => le_max_right _ _

lemma maximum_le_threshold_add_excess (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Instance.maximum x ≤ t + ∑ i, max (x i - t) 0 := by
  have hs : 0 ≤ ∑ i, max (x i - t) 0 := Finset.sum_nonneg fun _ _ => le_max_right _ _
  apply Instance.maximum_le x (add_nonneg ht hs)
  intro i
  have hi : max (x i - t) 0 ≤ ∑ j, max (x j - t) 0 :=
    Finset.single_le_sum (fun j _ => le_max_right (x j - t) 0) (Finset.mem_univ i)
  have hxi : x i - t ≤ max (x i - t) 0 := le_max_left _ _
  linarith

lemma Instance.expectedMaximum_le_threshold_add_excess (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {t : ℝ} (ht : 0 ≤ t) :
    P.expectedMaximum ≤ t + ∑ i, P.excessMean t i := by
  have hi (i : Fin n) : Integrable (fun x : ℝ => max (x - t) 0) (P.law i) :=
    ((P.integrable_maximum_iff.mp hP i).sub (integrable_const t)).pos_part
  have hworld (i : Fin n) : Integrable (fun x : Fin n → ℝ => max (x i - t) 0) P.valuesLaw :=
    (measurePreserving_eval P.law i).integrable_comp_of_integrable (hi i)
  have hsum : Integrable (fun x : Fin n → ℝ => ∑ i, max (x i - t) 0) P.valuesLaw :=
    integrable_finsetSum Finset.univ (fun i _ => hworld i)
  have h := integral_mono hP ((integrable_const t).add hsum)
    (fun x => maximum_le_threshold_add_excess x ht)
  change (∫ x, maximum x ∂P.valuesLaw) ≤ ∫ x, t + ∑ i, max (x i - t) 0 ∂P.valuesLaw at h
  rw [integral_add (μ := P.valuesLaw) (f := fun _ : Fin n → ℝ => t)
    (g := fun x : Fin n → ℝ => ∑ i : Fin n, max (x i - t) 0)
    (integrable_const t) hsum, integral_finsetSum Finset.univ (fun i _ => hworld i)] at h
  have heq (i : Fin n) : (∫ x : Fin n → ℝ, max (x i - t) 0 ∂P.valuesLaw) = P.excessMean t i := by
    have hm := (measurePreserving_eval P.law i).map_eq
    change P.valuesLaw.map (fun x => x i) = P.law i at hm
    have hf : Measurable (fun x : ℝ => max (x - t) 0) := (measurable_id.sub_const t).max measurable_const
    have hh := integral_map (μ := P.valuesLaw) (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
    rw [hm] at hh
    exact hh.symm
  simpa only [Instance.expectedMaximum, integral_const, probReal_univ, one_smul, heq] using h

/-- A positive-part excess is paid only at selection, and its mean factors through reach. -/
lemma constantThreshold_excess_reach_integral (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (t : ℝ) (i : Fin n) :
    let π := RandomizedPolicy.constantThreshold t n
    (∫ ω : π.World, max (ω.1 i - t) 0 *
      (if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0) ∂P.worldLaw π.seedLaw) =
      P.excessMean t i * π.rule.reachProbability P π.seedLaw i := by
  dsimp
  classical
  let π := RandomizedPolicy.constantThreshold t n
  haveI : Subsingleton π.Seed := by change Subsingleton Unit; infer_instance
  let μ := P.worldLaw π.seedLaw
  let I : π.World → ℝ := fun ω => if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  let F : ℝ → ℝ := fun x => max (x - t) 0
  have hF : Measurable F := (measurable_id.sub_const t).max measurable_const
  have hI : Measurable I := Measurable.ite
    (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    measurable_const measurable_const
  have hind := (ProphetSecretary.Probability.reachIndicator_value_independent P π.seedLaw i π.rule π.measurable_rule).comp
    measurable_id hF
  have hv : MeasurePreserving (fun ω : π.World => ω.1 i) μ (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  have hFw : Integrable (fun ω : π.World => F (ω.1 i)) μ :=
    hv.integrable_comp_of_integrable
      (((P.integrable_maximum_iff.mp hP i).sub (integrable_const t)).pos_part)
  have heq := hind.symm.integral_fun_mul_eq_mul_integral
    hFw.aestronglyMeasurable hI.aestronglyMeasurable
  have hX : (∫ ω, F (ω.1 i) ∂μ) = P.excessMean t i := by
    have h := integral_map (μ := μ) hv.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hv.map_eq] at h
    exact h.symm
  have hReach : (∫ ω, I ω ∂μ) = π.rule.reachProbability P π.seedLaw i := by
    simpa only [I, μ, Policy.reachProbability, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, Function.comp_def] using
      (integral_indicator_one (μ := μ)
        (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
          (fun j => (measurable_pi_apply j).comp measurable_fst)
          (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i))
  change (∫ ω : π.World, F (ω.1 i) * I ω ∂μ) =
    (∫ ω : π.World, F (ω.1 i) ∂μ) * (∫ ω : π.World, I ω ∂μ) at heq
  rw [hX, hReach] at heq
  exact heq

/-- A constant threshold's lower bound, with the failure probability kept explicit. -/
lemma constantThreshold_expectedReward_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (t : ℝ) (ht : 0 ≤ t) :
    ∃ p0 : ℝ, 0 ≤ p0 ∧ p0 ≤ 1 ∧
      t * (1 - p0) + p0 * (P.expectedMaximum - t) ≤
        (RandomizedPolicy.constantThreshold t n).expectedReward P := by
  classical
  let π := RandomizedPolicy.constantThreshold t n
  haveI : Subsingleton π.Seed := by change Subsingleton Unit; infer_instance
  let μ := P.worldLaw π.seedLaw
  let N : Set π.World := {ω | ∀ i, ω.1 i < t}
  let I : Fin n → π.World → ℝ := fun i ω => if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  let F : Fin n → π.World → ℝ := fun i ω => max (ω.1 i - t) 0
  have hNm : MeasurableSet N := by
    have hcoord (i : Fin n) : Measurable (fun ω : π.World => ω.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    simpa only [N, Set.setOf_forall] using
      (MeasurableSet.iInter fun i => measurableSet_lt (hcoord i) measurable_const)
  have hInd (S : Set π.World) (hS : MeasurableSet S) :
      (∫ ω, (if ω ∈ S then (1 : ℝ) else 0) ∂μ) = μ.real S := by
    simpa only [Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) hS)
  have hNint : (∫ ω : π.World, (if ω ∈ N then (1 : ℝ) else 0) ∂μ) = μ.real N := by
    simpa only [Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) hNm)
  have hQint : (∫ ω : π.World, (if ω ∈ Nᶜ then (1 : ℝ) else 0) ∂μ) = μ.real Nᶜ := by
    simpa only [Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) hNm.compl)
  have hIi (i : Fin n) : Measurable (I i) := Measurable.ite
    (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    measurable_const measurable_const
  have hII (i : Fin n) : Integrable (I i) μ := by
    apply Integrable.of_bound (hIi i).aestronglyMeasurable 1
    filter_upwards [] with ω
    dsimp [I]
    split_ifs <;> norm_num
  have hIeq (i : Fin n) : (∫ ω, I i ω ∂μ) = π.rule.reachProbability P π.seedLaw i := by
    exact hInd _ (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
  have hpq (i : Fin n) : μ.real N ≤ π.rule.reachProbability P π.seedLaw i := by
    have hNI : Integrable (fun ω : π.World => if ω ∈ N then (1 : ℝ) else 0) μ := by
      apply Integrable.of_bound
        (Measurable.ite hNm measurable_const measurable_const).aestronglyMeasurable 1
      filter_upwards [] with ω
      split_ifs <;> norm_num
    have h := integral_mono_ae hNI (hII i) ?_
    · rwa [hNint, hIeq] at h
    · filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw] with ω hω
      by_cases hn : ω ∈ N
      · have hr : π.rule.Reaches ω.2.2 ω.1 ω.2.1 i := by
          have hu : ω.2.2 = () := Subsingleton.elim _ _
          rw [hu]
          exact constantThresholdRule_reaches_of_no_qualifier t ω.1 ω.2.1 hn i (hω i).2
        simp only [if_pos hn, I, if_pos hr, le_refl]
      · have hnn : 0 ≤ I i ω := by dsimp [I]; split_ifs <;> norm_num
        simpa only [if_neg hn] using hnn
  have hFI (i : Fin n) : Integrable (F i) μ := by
    have hv : MeasurePreserving (fun ω : π.World => ω.1 i) μ (P.law i) :=
      (measurePreserving_eval P.law i).comp measurePreserving_fst
    exact hv.integrable_comp_of_integrable
      ((P.integrable_maximum_iff.mp hP i).sub (integrable_const t)).pos_part
  have hFm (i : Fin n) : Measurable (F i) := by
    have hx : Measurable (fun ω : π.World => ω.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    exact (hx.sub_const t).max measurable_const
  have hprod (i : Fin n) : Integrable (fun ω => F i ω * I i ω) μ := by
    apply (hFI i).mono' ((hFm i).mul (hIi i)).aestronglyMeasurable
    filter_upwards [] with ω
    dsimp [I, F]
    split_ifs <;> simp [abs_of_nonneg (le_max_right (ω.1 i - t) 0)]
  have hQm : Measurable (fun ω : π.World => if ω ∈ Nᶜ then (1 : ℝ) else 0) :=
    Measurable.ite hNm.compl measurable_const measurable_const
  have hQI : Integrable (fun ω : π.World => if ω ∈ Nᶜ then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound hQm.aestronglyMeasurable 1
    filter_upwards [] with ω
    split_ifs <;> norm_num
  have hreward : π.realizedReward =ᵐ[μ] fun ω =>
      t * (if ω ∈ Nᶜ then 1 else 0) + ∑ i, F i ω * I i ω := by
    filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw,
      P.world_clocks_distinct π.seedLaw] with ω hω hinj
    change (constantThresholdRule t n).reward ω.2.2 Finset.univ ω.1 ω.2.1 = _
    have hu : ω.2.2 = () := Subsingleton.elim _ _
    rw [hu, constantThresholdRule_reward_decomposition t ω.1 ω.2.1 (fun i => (hω i).2) hinj]
    have hqual : (∃ i, t ≤ ω.1 i) ↔ ω ∈ Nᶜ := by
      simp only [N, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt]
    simp only [hqual, I, F, hu, π, RandomizedPolicy.constantThreshold]
  have hsum : Integrable (fun ω : π.World => ∑ i, F i ω * I i ω) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hprod i)
  have hEq : π.expectedReward P = t * (1 - μ.real N) +
      ∑ i, P.excessMean t i * π.rule.reachProbability P π.seedLaw i := by
    change (∫ ω, π.realizedReward ω ∂μ) = _
    rw [integral_congr_ae hreward,
      integral_add (f := fun ω : π.World => t * (if ω ∈ Nᶜ then 1 else 0))
        (g := fun ω : π.World => ∑ i, F i ω * I i ω) (hQI.const_mul t) hsum,
      integral_const_mul, hQint, measureReal_compl hNm,
      probReal_univ, integral_finsetSum Finset.univ (fun i _ => hprod i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact constantThreshold_excess_reach_integral P hP t i
  refine ⟨μ.real N, ENNReal.toReal_nonneg, ?_, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using prob_le_one (μ := μ) (s := N))
  · rw [hEq]
    have hsumlo : μ.real N * (P.expectedMaximum - t) ≤
        ∑ i, P.excessMean t i * π.rule.reachProbability P π.seedLaw i := by
      have hmean := P.expectedMaximum_le_threshold_add_excess hP ht
      calc
        μ.real N * (P.expectedMaximum - t) ≤ μ.real N * ∑ i, P.excessMean t i :=
          mul_le_mul_of_nonneg_left (by linarith) ENNReal.toReal_nonneg
        _ = ∑ i, P.excessMean t i * μ.real N := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hpq i) (P.excessMean_nonnegative t i)
    linarith

/-- One constant threshold gives half of the expected maximum, without knowing arrival order. -/
theorem constantThreshold_half_guarantee (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    P.expectedMaximum / 2 ≤
      (RandomizedPolicy.constantThreshold (P.expectedMaximum / 2) n).expectedReward P := by
  obtain ⟨p0, _hp0, _hp1, h⟩ := constantThreshold_expectedReward_lower P hP
    (P.expectedMaximum / 2) (div_nonneg P.expectedMaximum_nonnegative (by norm_num))
  nlinarith

/-- The paper's classical lower bound on the optimal global competitive ratio. -/
theorem half_le_optimalCompetitiveRatio : (1 : ℝ) / 2 ≤ optimalCompetitiveRatio := by
  apply le_csInf competitiveRatios_nonempty
  rintro r ⟨n, P, hP, rfl⟩
  apply (le_div_iff₀ hP.2).mpr
  have h := scalarObjective_le_optimal
    (RandomizedPolicy.constantThreshold (P.expectedMaximum / 2) n) P hP.1 zero_le_one le_rfl
  rw [RandomizedPolicy.scalarObjective_eq _ P hP.1] at h
  have hg := constantThreshold_half_guarantee P hP.1
  nlinarith

end ProphetSecretary.Model

